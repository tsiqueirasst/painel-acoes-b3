import hashlib
import hmac
import html
import inspect
import io
import json
import math
import re
import secrets
import time
import xml.etree.ElementTree as ET
import zipfile
from concurrent.futures import ThreadPoolExecutor
from datetime import date, datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from urllib.parse import urlencode
import unicodedata

import pandas as pd
import plotly.graph_objects as go
import requests
import streamlit as st
import streamlit.components.v1 as components
import yfinance as yf
from bs4 import BeautifulSoup
from st_keyup import st_keyup

st.set_page_config(page_title="Painel Valuation B3", page_icon="📈", layout="wide")

BRT = timezone(timedelta(hours=-3))
HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
    )
}

BESST_SETORES = {
    "Intermediários Financeiros",
    "Energia Elétrica",
    "Água e Saneamento",
    "Previdência e Seguros",
    "Telecomunicações",
}

SETOR_ALIAS = {
    "Intermediários Financeiros": "Bancos (Intermediários Financeiros)",
    "Água e Saneamento": "Saneamento (Água e Saneamento)",
    "Previdência e Seguros": "Seguros e Previdência",
}
ALIAS_PARA_SETOR = {v: k for k, v in SETOR_ALIAS.items()}

SETOR_CURTO = {
    "Intermediários Financeiros": "Bancos",
    "Energia Elétrica": "Energia Elétrica",
    "Água e Saneamento": "Saneamento",
    "Previdência e Seguros": "Seguros",
    "Telecomunicações": "Telecomunicações",
}


def _norm_txt(s: str) -> str:
    return unicodedata.normalize("NFKD", s).encode("ascii", "ignore").decode("ascii").lower()


def limpar_nome_empresa(short_name: str, long_name: str, ticker: str) -> str:
    ln = " ".join((long_name or "").split())
    sn = " ".join((short_name or "").split())
    ln_low = ln.lower()

    if ln and (ln_low.startswith("banco ") or "banco " in ln_low or "unibanco" in ln_low or ln_low.startswith("caixa ")):
        limpo = re.sub(r"\((Brasil|Brazil)\)", "", ln, flags=re.IGNORECASE)
        limpo = re.sub(r"(?<!\w)(Holding|S\.A\.?|S/A|SA|Ltda\.?)(?!\w)", "", limpo, flags=re.IGNORECASE)
        limpo = re.sub(r"[,\-\.\s]+$", "", " ".join(limpo.split())).strip()
        if limpo:
            return limpo.upper()

    if sn:
        raw_sn = " ".join((short_name or "").split(" "))
        # Trata casos onde a B3/Yahoo cola o tipo (ON/PN/UNT) na 13ª posição
        if len(short_name or "") >= 13:
            s_pad = short_name
            if s_pad[12:15] in ("ON ", "PN ", "UNT", "PNA", "PNB", "PNC", "PND") or s_pad[12:14] in ("ON", "PN"):
                raw_sn = s_pad[:12] + " " + s_pad[12:]
        tokens_remover = {
            "ON", "PN", "PNA", "PNB", "PNC", "PND", "UNT",
            "N1", "N2", "NM", "MA", "MB", "ED", "EJ", "EDJ",
            "EB", "ES", "EX", "CI", "BDR", "DR1", "DR2", "DR3", "ATZ", "REC", "DIR",
        }
        partes = [p for p in raw_sn.split() if p.upper() not in tokens_remover]
        res = " ".join(partes).strip()
        if res:
            return res.upper()

    if ln:
        limpo = re.sub(r"(?<!\w)(S\.A\.?|S/A|SA|Ltda\.?)(?!\w)", "", ln, flags=re.IGNORECASE)
        limpo = re.sub(r"[,\-\.\s]+$", "", " ".join(limpo.split())).strip()
        if limpo:
            return limpo.upper()
    return ticker


# --- UTILITÁRIOS DE FORMATAÇÃO ---
def fmt_num(val: float, casas: int = 2) -> str:
    s = f"{val:,.{casas}f}"
    return s.replace(",", "X").replace(".", ",").replace("X", ".")


def fmt_bi_mi(val: float | None) -> str:
    if val is None or pd.isna(val):
        return "—"
    sinal = "-" if val < 0 else ""
    av = abs(float(val))
    if av >= 1e9:
        return f"{sinal}{fmt_num(av / 1e9)} BI"
    if av >= 1e6:
        return f"{sinal}{fmt_num(av / 1e6)} MI"
    if av >= 1e3:
        return f"{sinal}{fmt_num(av / 1e3)} mil"
    return f"{sinal}{fmt_num(av)}"


def parse_br_num(val: str) -> float | None:
    if val is None:
        return None
    s = str(val).strip().replace("%", "").replace(".", "").replace(",", ".")
    if not s or s == "-":
        return None
    try:
        return float(s)
    except ValueError:
        return None


# --- SECRETS, GIST PRIVADO & AUTENTICAÇÃO ---
def get_secret(key: str, default=None):
    try:
        return st.secrets[key]
    except Exception:
        return default


def gist_configurado() -> bool:
    return bool(get_secret("GITHUB_TOKEN") and get_secret("GIST_ID"))


def sso_configurado() -> bool:
    return get_secret("auth") is not None


def _gist_headers() -> dict:
    return {
        "Authorization": f"Bearer {get_secret('GITHUB_TOKEN')}",
        "Accept": "application/vnd.github+json",
    }


def ler_db_gist() -> tuple[dict, str]:
    gist_id = get_secret("GIST_ID")
    url = f"https://api.github.com/gists/{gist_id}"
    resp = requests.get(url, headers=_gist_headers(), timeout=15)
    resp.raise_for_status()
    data = resp.json()
    files = data.get("files", {})
    if not files:
        return {"usuarios": {}}, "dados_painel.json"
    filename = "dados_painel.json" if "dados_painel.json" in files else next(iter(files.keys()))
    conteudo = files[filename].get("content", "{}").strip() or "{}"
    try:
        db = json.loads(conteudo)
    except json.JSONDecodeError:
        db = {}
    if "usuarios" not in db or not isinstance(db["usuarios"], dict):
        db["usuarios"] = {}
    return db, filename


def salvar_db_gist(db: dict, filename: str):
    gist_id = get_secret("GIST_ID")
    url = f"https://api.github.com/gists/{gist_id}"
    payload = {"files": {filename: {"content": json.dumps(db, ensure_ascii=False, indent=2)}}}
    resp = requests.patch(url, headers=_gist_headers(), json=payload, timeout=15)
    resp.raise_for_status()


def hash_senha(senha: str, salt_hex: str | None = None) -> tuple[str, str]:
    salt = bytes.fromhex(salt_hex) if salt_hex else secrets.token_bytes(16)
    dk = hashlib.pbkdf2_hmac("sha256", senha.encode("utf-8"), salt, 100_000)
    return salt.hex(), dk.hex()


def verificar_senha(senha: str, salt_hex: str, hash_salvo: str) -> bool:
    if not salt_hex or not hash_salvo:
        return False
    _, novo_hash = hash_senha(senha, salt_hex)
    return hmac.compare_digest(novo_hash, hash_salvo)


def carregar_dados_usuario_nuvem(email: str):
    if not gist_configurado() or not email:
        return
    try:
        db, _ = ler_db_gist()
        u = db["usuarios"].get(email.lower(), {})
        favs = [str(x).upper() for x in u.get("favoritos", [])]
        lancs = u.get("lancamentos", [])
        st.session_state["favoritos"] = favs
        st.session_state["ms_favs"] = favs
        st.session_state["lancamentos"] = lancs
        st.session_state["nuvem_carregada_para"] = email.lower()
    except Exception:
        st.warning("Não foi possível carregar dados da nuvem. Confira seu GITHUB_TOKEN e GIST_ID nos Secrets.")


def salvar_dados_usuario_nuvem():
    email = st.session_state.get("usuario_email")
    if not gist_configurado() or not email:
        return
    try:
        db, filename = ler_db_gist()
        em = email.lower()
        u = db["usuarios"].get(em, {})
        u["favoritos"] = st.session_state.get("favoritos", [])
        u["lancamentos"] = st.session_state.get("lancamentos", [])
        db["usuarios"][em] = u
        salvar_db_gist(db, filename)
    except Exception:
        st.error("Erro ao salvar na nuvem. Confira suas credenciais nos Secrets.")


# --- NOTÍCIAS (GOOGLE NEWS RSS PT-BR) & SENTIMENTO ---
def _classificar_sentimento_noticia(titulo: str) -> tuple[str, str, float]:
    t = _norm_txt(titulo)

    critico_kw = (
        "recuperacao judicial", "pedido de falencia", "falencia", "fraude",
        "calote", "default", "cvm investiga", "investigada pela cvm",
        "investigacao da cvm", "pf investiga", "mpf investiga", "inadimpl",
        "rebaix", "rombo", "intervencao", "liquidacao extrajudicial",
    )
    if any(k in t for k in critico_kw):
        return "🚨 Risco Crítico", "critico", -5.0

    excecoes_prej = (
        "reverte prejuizo", "revertendo prejuizo", "sai de prejuizo",
        "saindo de prejuizo", "reduz prejuizo", "reduziu prejuizo",
        "diminui prejuizo", "menor prejuizo",
    )
    tem_prej_neg = ("prejuizo" in t) and not any(ex in t for ex in excecoes_prej)
    neg_kw = (
        "reverte lucro", "frustra", "abaixo do esperado", "abaixo das estimativas",
        "decepciona", "queda forte", "queda de receita", "queda na receita",
        "receita cai", "lucro cai", "lucro recua", "lucro desaba",
        "queda no lucro", "recuo no lucro", "corta dividendo", "suspende dividendo",
        "desaba", "derrete", "despenc", "tombo", "crise", "multa", "queda ", "cai ",
    )
    if tem_prej_neg or any(k in t for k in neg_kw):
        return "🔴 Atenção", "negativo", -2.5

    pos_kw = (
        "reverte prejuizo", "revertendo prejuizo", "sai de prejuizo", "reduz prejuizo",
        "dividendo", "jcp", "juros sobre capital", "provento",
        "lucro sobe", "lucro avanca", "lucro cresce", "lucro salta", "lucro dispara",
        "lucro recorde", "resultado recorde", "supera estimativas", "acima do esperado",
        "bate estimativas", "recorde", "dispara", "sobe ", "alta ", "aprova", "supera", "lucro",
    )
    if any(k in t for k in pos_kw):
        return "🟢 Positivo/Provento", "positivo", 2.5

    corp_kw = (
        "privatiz", "leilao", "fusao", "aquisicao", "compra ", "venda ",
        "fato relevante", "estatiz", "governo", "desestatiz", "recompra", "bonificacao",
    )
    if any(k in t for k in corp_kw):
        return "🏛️ Fato/Corporativo", "corporativo", 0.0

    return "📰 Notícia", "neutro", 0.0


def _classificar_noticia(titulo: str) -> str:
    return _classificar_sentimento_noticia(titulo)[0]


def analisar_sentimento_noticias(itens: list[dict], agora_ts: float | None = None) -> dict:
    if not itens:
        return {"news_score": 0.0, "news_resumo": "⚪ Neutro", "qtd_30d": 0, "qtd_7d": 0}

    agora = agora_ts if agora_ts is not None else time.time()
    limite_30d = agora - (30 * 86400)
    limite_7d = agora - (7 * 86400)

    soma_pts = 0.0
    qtd_30d = 0
    qtd_7d = 0
    cnt_critico = 0
    cnt_neg = 0
    cnt_pos = 0
    tem_rj = False
    tem_prej_ou_frustra = False
    tem_provento = False
    tem_balanco_pos = False

    for it in itens:
        ts = float(it.get("ts") or 0.0)
        if ts <= 0.0 or ts < limite_30d:
            continue

        qtd_30d += 1
        peso_tempo = 2.0 if ts >= limite_7d else 1.0
        if ts >= limite_7d:
            qtd_7d += 1

        titulo = it.get("titulo") or ""
        t_norm = _norm_txt(titulo)
        cat = it.get("sentimento_cat")
        pts = it.get("sentimento_pts")
        if cat is None or pts is None:
            _, cat, pts = _classificar_sentimento_noticia(titulo)

        soma_pts += float(pts) * peso_tempo
        if cat == "critico":
            cnt_critico += 1
            if "recuperacao judicial" in t_norm or "falencia" in t_norm:
                tem_rj = True
        elif cat == "negativo":
            cnt_neg += 1
            if any(k in t_norm for k in ("prejuizo", "reverte lucro", "frustra", "queda de receita", "queda na receita")):
                tem_prej_ou_frustra = True
        elif cat == "positivo":
            cnt_pos += 1
            if any(k in t_norm for k in ("dividendo", "jcp", "juros sobre capital", "provento")):
                tem_provento = True
            if any(k in t_norm for k in ("lucro", "resultado", "supera", "recorde", "reverte prejuizo")):
                tem_balanco_pos = True

    news_score = round(max(-10.0, min(10.0, soma_pts)), 1)

    if cnt_critico > 0:
        news_resumo = "🚨 Risco Crítico / RJ" if tem_rj else "🚨 Risco Crítico"
    elif news_score <= -2.0 or (cnt_neg > cnt_pos and news_score < 0.0):
        news_resumo = "🔴 Prejuízo Recente" if tem_prej_ou_frustra else "🔴 Notícias Negativas"
    elif news_score >= 2.0 or (cnt_pos > cnt_neg and news_score > 0.0):
        news_resumo = "🟢 Balanço / Proventos" if (tem_provento or tem_balanco_pos) else "🟢 Positivo"
    else:
        news_resumo = "⚪ Neutro"

    return {
        "news_score": news_score,
        "news_resumo": news_resumo,
        "qtd_30d": qtd_30d,
        "qtd_7d": qtd_7d,
    }


@st.cache_data(ttl=1800, show_spinner=False)
def buscar_noticias_lote(tickers_tuple: tuple[str, ...]) -> dict[str, list[dict]]:
    def _one(ticker: str):
        for q_str in (f'"{ticker}"', f"{ticker} ações"):
            try:
                url = "https://news.google.com/rss/search"
                params = {"q": q_str, "hl": "pt-BR", "gl": "BR", "ceid": "BR:pt-419"}
                resp = requests.get(url, params=params, headers=HEADERS, timeout=10)
                resp.raise_for_status()
                root = ET.fromstring(resp.content)
                itens = []
                for item in root.findall("./channel/item"):
                    titulo = (item.findtext("title") or "").strip()
                    link = (item.findtext("link") or "").strip()
                    pub = (item.findtext("pubDate") or "").strip()
                    fonte_el = item.find("source")
                    fonte = (fonte_el.text or "").strip() if fonte_el is not None else ""
                    if fonte and titulo.endswith(f" - {fonte}"):
                        titulo = titulo[: -len(f" - {fonte}")].strip()
                    dt_obj = None
                    dt_str = ""
                    if pub:
                        try:
                            dt_obj = parsedate_to_datetime(pub)
                            dt_str = dt_obj.astimezone(BRT).strftime("%d/%m/%Y %H:%M")
                        except Exception:
                            dt_str = pub
                    if titulo and link:
                        tag, cat, pts_s = _classificar_sentimento_noticia(titulo)
                        itens.append({
                            "titulo": titulo, "link": link, "fonte": fonte,
                            "data_str": dt_str, "tag": tag,
                            "sentimento_cat": cat, "sentimento_pts": pts_s,
                            "ts": dt_obj.timestamp() if dt_obj else 0.0,
                        })
                if itens:
                    itens.sort(key=lambda x: x["ts"], reverse=True)
                    return ticker, itens[:12]
            except Exception:
                continue
        return ticker, []

    out = {}
    if not tickers_tuple:
        return out
    with ThreadPoolExecutor(max_workers=12) as ex:
        for t, res in ex.map(_one, tickers_tuple):
            out[t] = res
    return out


def buscar_sentimento_noticias_lote(tickers_tuple: tuple[str, ...]) -> dict[str, dict]:
    noticias_lote = buscar_noticias_lote(tickers_tuple)
    agora_ts = time.time()
    out: dict[str, dict] = {}
    for tk in tickers_tuple:
        itens = noticias_lote.get(tk, [])
        analise = analisar_sentimento_noticias(itens, agora_ts=agora_ts)
        out[tk] = {**analise, "noticias": itens}
    return out


# --- DADOS B3 (FUNDAMENTUS, CVM & YAHOO) ---
@st.cache_data(ttl=86400, show_spinner=False)
def carregar_setores_fundamentus() -> dict[str, str]:
    url = "https://www.fundamentus.com.br/buscaavancada.php"
    resp = requests.get(url, headers=HEADERS, timeout=15)
    resp.raise_for_status()
    soup = BeautifulSoup(resp.text, "lxml")
    select = soup.find("select", {"name": "setor"})
    setores = {}
    if select:
        for opt in select.find_all("option"):
            val = (opt.get("value") or "").strip()
            nome = " ".join(opt.text.split())
            if val and nome:
                setores[nome] = val
    return setores


def _ler_tabela_fundamentus(url: str, session: requests.Session | None = None) -> list[dict]:
    cliente = session or requests
    resp = cliente.get(url, headers=HEADERS, timeout=20)
    resp.raise_for_status()
    if not resp.encoding or resp.encoding.lower() in ("ascii", "utf-8"):
        resp.encoding = "ISO-8859-1"
    soup = BeautifulSoup(resp.text, "lxml")
    tabela = soup.find("table", {"id": "resultado"})
    if not tabela:
        return []
    cabecalho = [th.get_text(strip=True) for th in tabela.find("thead").find_all("th")]
    registros = []
    tbody = tabela.find("tbody")
    if not tbody:
        return []
    for tr in tbody.find_all("tr"):
        celulas = [td.get_text(strip=True) for td in tr.find_all("td")]
        if len(celulas) == len(cabecalho):
            registros.append(dict(zip(cabecalho, celulas)))
    return registros


@st.cache_data(ttl=3600, show_spinner=False)
def buscar_detalhes_fundamentus(ticker: str) -> dict:
    try:
        url = f"https://www.fundamentus.com.br/detalhes.php?papel={ticker}"
        resp = requests.get(url, headers=HEADERS, timeout=15)
        resp.raise_for_status()
        soup = BeautifulSoup(resp.text, "lxml")
        dados = {}
        for tr in soup.find_all("tr"):
            tds = tr.find_all("td")
            i = 0
            while i + 1 < len(tds):
                cls_lbl = " ".join(tds[i].get("class", []))
                if "label" in cls_lbl:
                    lbl = tds[i].get_text(strip=True).lstrip("?").strip()
                    val = tds[i + 1].get_text(strip=True)
                    if lbl and lbl not in dados:
                        dados[lbl] = val
                    i += 2
                else:
                    i += 1
        return dados
    except Exception:
        return {}


@st.cache_data(ttl=86400, show_spinner=False)
def buscar_cambio_brl(moeda: str) -> pd.Series:
    if not moeda or moeda.upper() == "BRL":
        return pd.Series(dtype=float)
    try:
        tk_fx = yf.Ticker(f"{moeda.upper()}BRL=X")
        df_fx = tk_fx.history(period="6y", interval="1d")
        if df_fx is not None and not df_fx.empty:
            df_fx.index = pd.to_datetime(df_fx.index).tz_localize(None)
            return df_fx["Close"].dropna()
    except Exception:
        pass
    return pd.Series(dtype=float)


# --- MOTOR CVM DADOS ABERTOS (DFP + ITR) ---
@st.cache_data(ttl=86400, show_spinner=False)
def carregar_mapa_cvm_tickers() -> tuple[dict[str, str], dict[str, str]]:
    """Retorna (mapa_ticker_para_cnpj, mapa_cd_cvm_para_cnpj)."""
    ano_atual = datetime.now(BRT).year
    mapa_tk: dict[str, str] = {}
    mapa_cod: dict[str, str] = {}
    pat_tk = re.compile(r"^[A-Z]{4}\d{1,2}$")

    for ano in (ano_atual, ano_atual - 1, ano_atual - 2):
        try:
            url = f"https://dados.cvm.gov.br/dados/CIA_ABERTA/DOC/FCA/DADOS/fca_cia_aberta_{ano}.zip"
            resp = requests.get(url, headers=HEADERS, timeout=25)
            if resp.status_code != 200:
                continue
            with zipfile.ZipFile(io.BytesIO(resp.content)) as zf:
                alvos = [n for n in zf.namelist() if "valor_mobiliario" in n.lower() and n.lower().endswith(".csv")]
                if not alvos:
                    continue
                with zf.open(alvos[0]) as f:
                    df = pd.read_csv(f, sep=";", encoding="latin-1", dtype=str)
                col_map = {c.lower(): c for c in df.columns}
                c_tk = col_map.get("codigo_negociacao")
                c_cnpj = col_map.get("cnpj_companhia")
                c_fim = col_map.get("data_fim_negociacao")
                c_ref = col_map.get("data_referencia")
                if not c_tk or not c_cnpj:
                    continue
                if c_ref:
                    df = df.sort_values(c_ref, ascending=True)
                for _, row in df.iterrows():
                    tk_val = str(row.get(c_tk) or "").strip().upper()
                    cnpj_val = str(row.get(c_cnpj) or "").strip()
                    if not pat_tk.match(tk_val) or not cnpj_val:
                        continue
                    fim_val = str(row.get(c_fim) or "").strip() if c_fim else ""
                    if fim_val and fim_val < f"{ano - 1}-01-01" and tk_val in mapa_tk:
                        continue
                    mapa_tk[tk_val] = cnpj_val
            if mapa_tk:
                break
        except Exception:
            continue

    try:
        resp_cad = requests.get(
            "https://dados.cvm.gov.br/dados/CIA_ABERTA/CAD/DADOS/cad_cia_aberta.csv",
            headers=HEADERS,
            timeout=20,
        )
        if resp_cad.status_code == 200:
            df_cad = pd.read_csv(
                io.BytesIO(resp_cad.content),
                sep=";",
                encoding="latin-1",
                dtype=str,
                usecols=lambda c: c in {"CNPJ_CIA", "CD_CVM", "SIT"},
            )
            for _, row in df_cad.iterrows():
                cnpj_c = str(row.get("CNPJ_CIA") or "").strip()
                cd_c = str(row.get("CD_CVM") or "").strip().lstrip("0")
                if cnpj_c and cd_c:
                    mapa_cod[cd_c] = cnpj_c
    except Exception:
        pass

    return mapa_tk, mapa_cod


def _ler_df_cvm_zip(zf: zipfile.ZipFile, padrao_nome: str, tipo_doc: str) -> pd.DataFrame:
    alvos = [n for n in zf.namelist() if padrao_nome in n and n.lower().endswith(".csv")]
    if not alvos:
        return pd.DataFrame()
    nome_csv = alvos[0]

    with zf.open(nome_csv) as f_head:
        cols_disp = list(pd.read_csv(f_head, sep=";", encoding="latin-1", nrows=0).columns)

    desejadas = ["CNPJ_CIA", "VERSAO", "DT_REFER", "DT_INI_EXERC", "DT_FIM_EXERC", "ORDEM_EXERC", "CD_CONTA", "DS_CONTA", "VL_CONTA", "ESCALA_MOEDA"]
    usecols = [c for c in desejadas if c in cols_disp]
    dtype_map = {c: str for c in usecols if c not in ("VERSAO", "VL_CONTA")}

    partes = []
    with zf.open(nome_csv) as f:
        for chunk in pd.read_csv(f, sep=";", encoding="latin-1", usecols=usecols, dtype=dtype_map, chunksize=100_000):
            if "ORDEM_EXERC" in chunk.columns:
                chunk = chunk[chunk["ORDEM_EXERC"] == "ÚLTIMO"]
            if chunk.empty:
                continue

            cd = chunk["CD_CONTA"].fillna("").str.strip()
            ds = chunk["DS_CONTA"].fillna("").str.lower()

            if tipo_doc == "DRE":
                mask = cd.isin({"3.01", "3.03", "3.05", "3.11", "3.11.01", "3.13"}) | (
                    (cd.str.len() <= 7) & cd.str.startswith("3.") & ds.str.contains("lucro|preju|resultado líq|resultado liq", regex=True)
                )
            elif tipo_doc == "BPA":
                mask = cd.isin({"1.01.01", "1.01.02"})
            elif tipo_doc == "BPP":
                mask = cd.isin({"2.01.04", "2.02.01", "2.03", "2.03.09", "2.07", "2.07.01", "2.07.02"}) | (
                    (cd.str.len() <= 7) & cd.str.startswith("2.") & ds.str.contains("patrimônio l|patrimonio l", regex=True)
                )
            elif tipo_doc == "DFC_MI":
                mask = cd.str.startswith("6.01") & ds.str.contains("deprecia|amortiza|exaust", regex=True)
            else:
                mask = pd.Series(False, index=chunk.index)

            sub = chunk[mask].copy()
            if sub.empty:
                continue
            sub["CD_CONTA"] = cd[mask]
            sub["DS_CONTA"] = sub["DS_CONTA"].fillna("").str.strip()
            sub["CNPJ_CIA"] = sub["CNPJ_CIA"].fillna("").str.strip()
            sub["VL_CONTA"] = pd.to_numeric(sub["VL_CONTA"], errors="coerce")
            sub = sub.dropna(subset=["VL_CONTA"])
            if "ESCALA_MOEDA" in sub.columns:
                mult = sub["ESCALA_MOEDA"].fillna("").str.upper().map(lambda x: 1000.0 if x == "MIL" else 1.0)
                sub["VL_CONTA"] = sub["VL_CONTA"] * mult
            else:
                sub["VL_CONTA"] = sub["VL_CONTA"] * 1000.0
            if "VERSAO" in sub.columns:
                sub["VERSAO"] = pd.to_numeric(sub["VERSAO"], errors="coerce").fillna(1)
            else:
                sub["VERSAO"] = 1
            partes.append(sub)

    if not partes:
        return pd.DataFrame()
    return pd.concat(partes, ignore_index=True)


def _consolidar_registros_cvm(df_con: pd.DataFrame, df_ind: pd.DataFrame, eh_fluxo: bool = False) -> dict[tuple[str, str], dict]:
    """Agrupa registros por (CNPJ_CIA, DT_REFER) mantendo consolidado > individual e última versão."""
    out: dict[tuple[str, str], dict] = {}
    for prioridade, df in ((1, df_ind), (2, df_con)):
        if df is None or df.empty:
            continue
        if eh_fluxo and "DT_INI_EXERC" in df.columns and "DT_FIM_EXERC" in df.columns:
            dt_ini = pd.to_datetime(df["DT_INI_EXERC"], errors="coerce")
            dt_fim = pd.to_datetime(df["DT_FIM_EXERC"], errors="coerce")
            df = df.assign(_span=(dt_fim - dt_ini).dt.days.fillna(0))
            df = df.sort_values(["VERSAO", "_span"], ascending=[True, True])
        else:
            df = df.sort_values("VERSAO", ascending=True)

        # Para cada (CNPJ, DT_REFER, CD_CONTA) a última linha (maior VERSAO e maior _span YTD) vence
        df = df.drop_duplicates(subset=["CNPJ_CIA", "DT_REFER", "CD_CONTA"], keep="last")

        for row in df.itertuples(index=False):
            key = (row.CNPJ_CIA, row.DT_REFER)
            if key not in out:
                out[key] = {"_prio": prioridade, "contas": {}}
            elif prioridade < out[key]["_prio"]:
                continue
            elif prioridade > out[key]["_prio"]:
                out[key] = {"_prio": prioridade, "contas": {}}
            out[key]["contas"][row.CD_CONTA] = (row.DS_CONTA, float(row.VL_CONTA))
    return out


def _extrair_metricas_periodo(dre_c: dict, bpa_c: dict, bpp_c: dict, dfc_c: dict) -> dict | None:
    def _val(contas: dict, cd: str) -> float | None:
        it = contas.get(cd)
        return it[1] if it is not None else None

    def _ds(contas: dict, cd: str) -> str:
        it = contas.get(cd)
        return it[0].lower() if it is not None else ""

    rec = _val(dre_c, "3.01")
    lbr = _val(dre_c, "3.03")
    ebit = _val(dre_c, "3.05")

    lliq = None
    for cand_ll in ("3.11", "3.13", "3.11.01"):
        if cand_ll in dre_c:
            ds_ll = _ds(dre_c, cand_ll)
            if any(k in ds_ll for k in ("lucro", "preju", "resultado")):
                lliq = _val(dre_c, cand_ll)
                break
    if lliq is None:
        for cd_k, (ds_k, vl_k) in dre_c.items():
            d_low = ds_k.lower()
            if "lucro" in d_low or "preju" in d_low:
                if "consolidado" in d_low or "do período" in d_low or "do periodo" in d_low:
                    lliq = vl_k
                    break

    if rec is None and lliq is None and not bpp_c:
        return None

    # Patrimônio Líquido (compatível com empresas padrão 2.03 e bancos IFRS 9 2.07)
    patr = None
    # 1) Conta específica "Patrimônio Líquido Atribuído aos Controladores" (ex: 2.07.01)
    for cd_k, (ds_k, vl_k) in sorted(bpp_c.items()):
        d_low = ds_k.lower()
        if ("patrimônio l" in d_low or "patrimonio l" in d_low) and ("controlador" in d_low) and ("não" not in d_low and "nao" not in d_low):
            patr = vl_k
            break
    # 2) Conta 2.07 ou 2.03 desde que a descrição seja de fato Patrimônio Líquido (não Provisões)
    if patr is None:
        for cd_base, cd_nc in (("2.07", "2.07.02"), ("2.03", "2.03.09")):
            if cd_base in bpp_c and "patrim" in _ds(bpp_c, cd_base):
                pl_tot = _val(bpp_c, cd_base)
                pl_nc = _val(bpp_c, cd_nc)
                if pl_nc is not None and "não control" in _ds(bpp_c, cd_nc).replace("nao", "não"):
                    patr = pl_tot - pl_nc
                else:
                    patr = pl_tot
                break
    # 3) Fallback por descrição contendo patrimônio líquido
    if patr is None:
        for cd_k, (ds_k, vl_k) in sorted(bpp_c.items()):
            d_low = ds_k.lower()
            if ("patrimônio l" in d_low or "patrimonio l" in d_low) and ("não control" not in d_low and "nao control" not in d_low):
                patr = vl_k
                break

    # Dívida Líquida = (Empréstimos & Financiamentos CP + LP, que já incluem arrendamentos na CVM) - (Caixa + Aplicações)
    div_cp = _val(bpp_c, "2.01.04")
    div_lp = _val(bpp_c, "2.02.01")
    cx1 = _val(bpa_c, "1.01.01")
    cx2 = _val(bpa_c, "1.01.02")
    div_liq = None
    if div_cp is not None or div_lp is not None:
        div_bruta = (div_cp or 0.0) + (div_lp or 0.0)
        disp = (cx1 or 0.0) + (cx2 or 0.0)
        div_liq = div_bruta - disp

    # Depreciação & Amortização (DFC_MI) evitando dupla contagem entre conta pai e conta filha
    da = None
    if dfc_c:
        cods_ord = sorted(dfc_c.keys(), key=lambda x: (len(x), x))
        mantidos = []
        for c in cods_ord:
            if not any(c.startswith(m + ".") for m in mantidos):
                mantidos.append(c)
        soma_da = sum(dfc_c[c][1] for c in mantidos)
        if soma_da < 0 and ebit is not None and ebit > 0:
            soma_da = abs(soma_da)
        da = soma_da

    ebitda = (ebit + da) if (ebit is not None and da is not None) else None

    return {
        "rec": rec,
        "lbr": lbr,
        "ebit": ebit,
        "lliq": lliq,
        "patr": patr,
        "div_liq": div_liq,
        "da": da,
        "ebitda": ebitda,
    }


@st.cache_data(ttl=86400, show_spinner=False)
def carregar_cvm_doc_ano(tipo: str, ano: int) -> dict[tuple[str, str], dict]:
    """Baixa e resume DFP ou ITR de um ano da CVM por (CNPJ_CIA, DT_REFER)."""
    base = "DFP" if tipo == "DFP" else "ITR"
    url = f"https://dados.cvm.gov.br/dados/CIA_ABERTA/DOC/{base}/DADOS/{tipo.lower()}_cia_aberta_{ano}.zip"
    try:
        resp = requests.get(url, headers=HEADERS, timeout=45)
        if resp.status_code != 200:
            return {}
        with zipfile.ZipFile(io.BytesIO(resp.content)) as zf:
            pref = f"{tipo.lower()}_cia_aberta"
            dre_m = _consolidar_registros_cvm(
                _ler_df_cvm_zip(zf, f"{pref}_DRE_con", "DRE"),
                _ler_df_cvm_zip(zf, f"{pref}_DRE_ind", "DRE"),
                eh_fluxo=True,
            )
            bpa_m = _consolidar_registros_cvm(
                _ler_df_cvm_zip(zf, f"{pref}_BPA_con", "BPA"),
                _ler_df_cvm_zip(zf, f"{pref}_BPA_ind", "BPA"),
                eh_fluxo=False,
            )
            bpp_m = _consolidar_registros_cvm(
                _ler_df_cvm_zip(zf, f"{pref}_BPP_con", "BPP"),
                _ler_df_cvm_zip(zf, f"{pref}_BPP_ind", "BPP"),
                eh_fluxo=False,
            )
            dfc_m = _consolidar_registros_cvm(
                _ler_df_cvm_zip(zf, f"{pref}_DFC_MI_con", "DFC_MI"),
                _ler_df_cvm_zip(zf, f"{pref}_DFC_MI_ind", "DFC_MI"),
                eh_fluxo=True,
            )

        chaves = set(dre_m.keys()) | set(bpp_m.keys())
        resumo: dict[tuple[str, str], dict] = {}
        for k in chaves:
            met = _extrair_metricas_periodo(
                dre_m.get(k, {}).get("contas", {}),
                bpa_m.get(k, {}).get("contas", {}),
                bpp_m.get(k, {}).get("contas", {}),
                dfc_m.get(k, {}).get("contas", {}),
            )
            if met is not None:
                resumo[k] = met
        return resumo
    except Exception:
        return {}


def buscar_dados_cvm_empresa(ticker: str, det_fund: dict) -> tuple[dict[int, dict], dict | None]:
    """Retorna (anuais_por_ano, ttm_cvm) direto da CVM em R$."""
    mapa_tk, mapa_cod = carregar_mapa_cvm_tickers()
    cnpj = mapa_tk.get(ticker)
    if not cnpj:
        return {}, None

    ano_atual = datetime.now(BRT).year
    anos_dfp = list(range(ano_atual - 5, ano_atual + 1))

    with ThreadPoolExecutor(max_workers=4) as ex:
        dfps_lista = list(ex.map(lambda a: (a, carregar_cvm_doc_ano("DFP", a)), anos_dfp))

    anuais: dict[int, dict] = {}
    for _, dados_ano in dfps_lista:
        for (c_cnpj, dt_ref), met in dados_ano.items():
            if c_cnpj == cnpj:
                yr = int(str(dt_ref)[:4])
                anuais[yr] = met

    if not anuais:
        return {}, None

    # TTM via CVM: DFP(último_ano) + ITR_atual - ITR_mesmo_trimestre_ano_anterior
    ttm_cvm = None
    ult_yr = max(anuais.keys())
    with ThreadPoolExecutor(max_workers=2) as ex:
        fut_curr = ex.submit(carregar_cvm_doc_ano, "ITR", ult_yr + 1)
        fut_prev = ex.submit(carregar_cvm_doc_ano, "ITR", ult_yr)
        itr_curr = fut_curr.result()
        itr_prev = fut_prev.result()

    datas_curr = sorted([dt_ref for (c_cnpj, dt_ref) in itr_curr.keys() if c_cnpj == cnpj])
    if datas_curr:
        dt_ult_itr = datas_curr[-1]
        mm_dd = dt_ult_itr[4:]
        dt_prev_itr = f"{ult_yr}{mm_dd}"
        met_curr = itr_curr.get((cnpj, dt_ult_itr))
        met_prev = itr_prev.get((cnpj, dt_prev_itr))
        met_dfp = anuais.get(ult_yr)

        if met_curr and met_prev and met_dfp:
            def _ttm_flow(k: str) -> float | None:
                v_dfp, v_c, v_p = met_dfp.get(k), met_curr.get(k), met_prev.get(k)
                if v_dfp is not None and v_c is not None and v_p is not None:
                    return v_dfp + v_c - v_p
                return None

            ebit_ttm = _ttm_flow("ebit")
            da_ttm = _ttm_flow("da")
            ebitda_ttm = (ebit_ttm + da_ttm) if (ebit_ttm is not None and da_ttm is not None) else _ttm_flow("ebitda")
            ttm_cvm = {
                "dt_ref": dt_ult_itr,
                "rec": _ttm_flow("rec"),
                "lbr": _ttm_flow("lbr"),
                "lliq": _ttm_flow("lliq"),
                "ebitda": ebitda_ttm,
                "patr": met_curr.get("patr"),
                "div_liq": met_curr.get("div_liq"),
                "ytd_rec": met_curr.get("rec"),
                "ytd_lbr": met_curr.get("lbr"),
                "ytd_lliq": met_curr.get("lliq"),
                "ytd_ebitda": met_curr.get("ebitda"),
            }

    return anuais, ttm_cvm


@st.cache_data(ttl=900, show_spinner=False)
def _carregar_todos_ativos_b3_cached(_v: int = 3) -> list[dict]:
    linhas = _ler_tabela_fundamentus("https://www.fundamentus.com.br/resultado.php")
    ativos = []
    for row in linhas:
        papel = row.get("Papel", "").strip().upper()
        cotacao = parse_br_num(row.get("Cotação"))
        if not papel or not cotacao or cotacao <= 0:
            continue

        pl = parse_br_num(row.get("P/L"))
        pvp = parse_br_num(row.get("P/VP"))
        dy = parse_br_num(row.get("Div.Yield")) or 0.0
        roe = parse_br_num(row.get("ROE"))
        liq_2m = parse_br_num(row.get("Liq.2meses")) or 0.0
        ev_ebitda = parse_br_num(row.get("EV/EBITDA") or row.get("EV / EBITDA"))
        ev_ebit = parse_br_num(row.get("EV/EBIT") or row.get("EV / EBIT"))
        roic = parse_br_num(row.get("ROIC"))
        marg_liq = parse_br_num(row.get("Mrg. Líq.") or row.get("Mrg Líq."))
        marg_ebit = parse_br_num(row.get("Mrg Ebit") or row.get("Mrg. Ebit"))
        liq_corr = parse_br_num(row.get("Liq. Corr."))
        div_brut_patrim = parse_br_num(row.get("Dív.Brut/ Patrim.") or row.get("Dív.Líq/ Patrim."))
        cresc_rec_5a = parse_br_num(row.get("Cresc. Rec.5a") or row.get("Cresc. Rec. 5a"))

        lpa = (cotacao / pl) if (pl is not None and pl != 0) else None
        vpa = (cotacao / pvp) if (pvp is not None and pvp != 0) else None
        dpa_12m = cotacao * (dy / 100.0)

        ativos.append({
            "ticker": papel, "nome": papel, "cotacao": cotacao, "dy_12m": dy,
            "pl": pl, "pvp": pvp, "roe": roe, "lpa": lpa, "vpa": vpa,
            "dpa_12m": dpa_12m, "liq_2m": liq_2m,
            "ev_ebitda": ev_ebitda, "ev_ebit": ev_ebit, "roic": roic,
            "marg_liq": marg_liq, "marg_ebit": marg_ebit, "liq_corr": liq_corr,
            "div_brut_patrim": div_brut_patrim, "cresc_rec_5a": cresc_rec_5a,
        })
    if not ativos:
        raise RuntimeError("Lista de ativos vazia do Fundamentus")
    return ativos


def carregar_todos_ativos_b3() -> list[dict]:
    return _carregar_todos_ativos_b3_cached()


@st.cache_data(ttl=86400, show_spinner=False)
def carregar_tickers_por_setor(setor_ids: tuple[str, ...], _v: int = 4) -> dict[str, str]:
    if not setor_ids:
        return {}
    mapa_setor: dict[str, str] = {}
    setores_dict = carregar_setores_fundamentus()
    id_para_nome = {v: k for k, v in setores_dict.items()}

    def _one_setor(sid: str):
        url_s = f"https://www.fundamentus.com.br/resultado.php?setor={sid}"
        for tentativa in range(2):
            try:
                linhas = _ler_tabela_fundamentus(url_s)
                return sid, [row.get("Papel", "").strip().upper() for row in linhas if row.get("Papel", "").strip()]
            except Exception:
                if tentativa == 0:
                    time.sleep(0.25)
        return sid, []

    with ThreadPoolExecutor(max_workers=8) as ex:
        for sid, papeis in ex.map(_one_setor, setor_ids):
            nome_setor = id_para_nome.get(sid, f"Setor {sid}")
            for papel in papeis:
                mapa_setor[papel] = nome_setor
    return mapa_setor


@st.cache_data(ttl=86400, show_spinner=False)
def carregar_mapa_todos_setores(_v: int = 4) -> dict[str, str]:
    setores_dict = carregar_setores_fundamentus()
    return carregar_tickers_por_setor(tuple(setores_dict.values()), _v=_v)


def _fetch_yf(ticker: str) -> tuple[str, dict]:
    try:
        tk = yf.Ticker(f"{ticker}.SA")
        info = tk.info or {}
        nome = limpar_nome_empresa(info.get("shortName", ""), info.get("longName", ""), ticker)

        cot_yf = None
        try:
            fi = tk.fast_info
            if fi:
                cot_yf = fi.get("lastPrice") or fi.get("regularMarketPrice")
        except Exception:
            pass
        if not cot_yf:
            cot_yf = info.get("currentPrice") or info.get("regularMarketPrice")

        ifr_14 = None
        mm20 = None
        mm50 = None
        mm200 = None
        dist_mm50_pct = None
        dist_mm200_pct = None
        dist_max_52s_pct = None
        razao_volume = None

        try:
            hist_1y = tk.history(period="1y", interval="1d", auto_adjust=False)
            if hist_1y is not None and not hist_1y.empty and "Close" in hist_1y.columns:
                close_s = hist_1y["Close"].dropna()
                if not cot_yf and not close_s.empty:
                    cot_yf = float(close_s.iloc[-1])

                px_ref = float(cot_yf) if cot_yf else (float(close_s.iloc[-1]) if not close_s.empty else None)

                if len(close_s) >= 15:
                    delta = close_s.diff().dropna()
                    gain = delta.clip(lower=0.0)
                    loss = (-delta).clip(lower=0.0)
                    avg_gain = float(gain.iloc[:14].mean())
                    avg_loss = float(loss.iloc[:14].mean())
                    for g_val, l_val in zip(gain.iloc[14:], loss.iloc[14:]):
                        avg_gain = (avg_gain * 13.0 + float(g_val)) / 14.0
                        avg_loss = (avg_loss * 13.0 + float(l_val)) / 14.0
                    if avg_loss == 0.0:
                        ifr_14 = 100.0 if avg_gain > 0.0 else 50.0
                    else:
                        rs = avg_gain / avg_loss
                        ifr_14 = 100.0 - (100.0 / (1.0 + rs))

                if len(close_s) >= 20:
                    mm20 = float(close_s.tail(20).mean())
                if len(close_s) >= 50:
                    mm50 = float(close_s.tail(50).mean())
                    if px_ref and mm50 > 0:
                        dist_mm50_pct = ((px_ref / mm50) - 1.0) * 100.0
                if len(close_s) >= 200:
                    mm200 = float(close_s.tail(200).mean())
                    if px_ref and mm200 > 0:
                        dist_mm200_pct = ((px_ref / mm200) - 1.0) * 100.0

                high_s = hist_1y["High"].dropna() if "High" in hist_1y.columns else pd.Series(dtype=float)
                max_52s = float(high_s.max()) if not high_s.empty else (float(close_s.max()) if not close_s.empty else None)
                if px_ref and max_52s and max_52s > 0:
                    dist_max_52s_pct = ((px_ref / max_52s) - 1.0) * 100.0

                if "Volume" in hist_1y.columns:
                    vol_s = hist_1y["Volume"].dropna()
                    if len(vol_s) >= 60:
                        vol_5d = float(vol_s.tail(5).mean())
                        vol_60d = float(vol_s.tail(60).mean())
                        if vol_60d > 0:
                            razao_volume = vol_5d / vol_60d
        except Exception:
            pass

        fin_curr = (info.get("financialCurrency") or "BRL").upper()
        lpa = info.get("trailingEps") if fin_curr == "BRL" else None
        vpa = info.get("bookValue") if fin_curr == "BRL" else None
        roe_raw = info.get("returnOnEquity")
        roe = (roe_raw * 100) if roe_raw is not None else None

        divs = tk.dividends
        dpa_12m = None
        dpa_med_6a = None
        anos_hist = 0

        if divs is not None and not divs.empty:
            divs.index = pd.to_datetime(divs.index).tz_localize(None)
            hoje = pd.Timestamp.now().tz_localize(None)
            dpa_12m = float(divs[divs.index >= (hoje - timedelta(days=365))].sum())
            ano_atual = hoje.year
            anos_validos = [a for a in range(ano_atual - 6, ano_atual)]
            divs_6a = divs[divs.index.year.isin(anos_validos)]
            if not divs_6a.empty:
                por_ano = divs_6a.groupby(divs_6a.index.year).sum()
                anos_hist = len(por_ano)
                dpa_med_6a = float(divs_6a.sum() / min(6, max(1, anos_hist)))

        payout = info.get("payoutRatio")
        div_rate = info.get("dividendRate")
        if lpa and lpa > 0 and payout and 0 < payout <= 1.2:
            dpa_proj = float(lpa * min(payout, 1.0))
        elif div_rate and div_rate > 0:
            dpa_proj = float(div_rate)
        elif dpa_12m is not None:
            dpa_proj = dpa_12m
        else:
            dpa_proj = None

        return ticker, {
            "nome": nome,
            "cotacao_yf": float(cot_yf) if cot_yf else None,
            "lpa_yf": float(lpa) if lpa is not None else None,
            "vpa_yf": float(vpa) if vpa is not None else None,
            "roe_yf": float(roe) if roe is not None else None,
            "dpa_12m_yf": float(dpa_12m) if dpa_12m is not None else None,
            "dpa_med_6a": float(dpa_med_6a) if dpa_med_6a is not None else None,
            "anos_hist": anos_hist,
            "dpa_proj": float(dpa_proj) if dpa_proj is not None else None,
            "ifr_14": float(ifr_14) if ifr_14 is not None else None,
            "mm20": float(mm20) if mm20 is not None else None,
            "mm50": float(mm50) if mm50 is not None else None,
            "mm200": float(mm200) if mm200 is not None else None,
            "dist_mm50_pct": float(dist_mm50_pct) if dist_mm50_pct is not None else None,
            "dist_mm200_pct": float(dist_mm200_pct) if dist_mm200_pct is not None else None,
            "dist_max_52s_pct": float(dist_max_52s_pct) if dist_max_52s_pct is not None else None,
            "razao_volume": float(razao_volume) if razao_volume is not None else None,
        }
    except Exception:
        return ticker, {}


@st.cache_data(ttl=300, show_spinner=False)
def buscar_yahoo_lote(tickers_tuple: tuple[str, ...]) -> dict[str, dict]:
    if not tickers_tuple:
        return {}
    resultados = {}
    with ThreadPoolExecutor(max_workers=8) as executor:
        for ticker, dados in executor.map(_fetch_yf, tickers_tuple):
            resultados[ticker] = dados
    return resultados


@st.cache_data(ttl=300, show_spinner=False)
def buscar_historico_preco(ticker: str, periodo_label: str, ajustada: bool) -> pd.Series:
    tk = yf.Ticker(f"{ticker}.SA")
    if periodo_label == "1 D":
        df = tk.history(period="5d", interval="15m", auto_adjust=ajustada)
        if not df.empty:
            df.index = pd.to_datetime(df.index).tz_localize(None)
            df = df[df.index.date == df.index.date[-1]]
    elif periodo_label == "7 D":
        df = tk.history(period="1mo", interval="1h", auto_adjust=ajustada)
        if not df.empty:
            df.index = pd.to_datetime(df.index).tz_localize(None)
            df = df[df.index >= (df.index.max() - timedelta(days=7))]
    elif periodo_label == "15 A":
        df = tk.history(period="max", interval="1d", auto_adjust=ajustada)
        if not df.empty:
            df.index = pd.to_datetime(df.index).tz_localize(None)
            df = df[df.index >= (df.index.max() - pd.DateOffset(years=15))]
    else:
        mapa = {"30 D": "1mo", "6 M": "6mo", "YTD": "ytd", "1 A": "1y", "5 A": "5y", "10 A": "10y"}
        df = tk.history(period=mapa.get(periodo_label, "1y"), interval="1d", auto_adjust=ajustada)
        if not df.empty:
            df.index = pd.to_datetime(df.index).tz_localize(None)

    if df is None or df.empty:
        return pd.Series(dtype=float)
    return df["Close"].dropna()


@st.cache_data(ttl=1800, show_spinner=False)
def buscar_serie_max_ajustada(ticker: str) -> pd.Series:
    tk = yf.Ticker(f"{ticker}.SA")
    df = tk.history(period="max", interval="1d", auto_adjust=True)
    if df is None or df.empty:
        return pd.Series(dtype=float)
    df.index = pd.to_datetime(df.index).tz_localize(None)
    return df["Close"].dropna()


@st.cache_data(ttl=1800, show_spinner=False)
def buscar_divs_e_precos_carteira(tickers_tuple: tuple[str, ...]) -> dict[str, dict]:
    def _one(t: str):
        try:
            tk = yf.Ticker(f"{t}.SA")
            hist = tk.history(period="2y", interval="1d", auto_adjust=False)
            px = hist["Close"].dropna() if (hist is not None and not hist.empty) else pd.Series(dtype=float)
            if not px.empty:
                px.index = pd.to_datetime(px.index).tz_localize(None)
            divs = tk.dividends
            if divs is not None and not divs.empty:
                divs.index = pd.to_datetime(divs.index).tz_localize(None)
            else:
                divs = pd.Series(dtype=float)
            return t, {"px": px, "divs": divs}
        except Exception:
            return t, {"px": pd.Series(dtype=float), "divs": pd.Series(dtype=float)}

    out = {}
    with ThreadPoolExecutor(max_workers=8) as ex:
        for t, res in ex.map(_one, tickers_tuple):
            out[t] = res
    return out


def _pick_row(df: pd.DataFrame, candidatos: list[str], col) -> float | None:
    if df is None or df.empty or col not in df.columns:
        return None
    idx_map = {str(i).strip().lower(): i for i in df.index}
    for cand in candidatos:
        key = cand.lower()
        if key in idx_map:
            val = df.loc[idx_map[key], col]
            if pd.notna(val):
                return float(val)
    return None


@st.cache_data(ttl=900, show_spinner=False)
def buscar_historico_fundamentalista(
    ticker: str,
    cot_live: float | None = None,
    pl_live: float | None = None,
    pvp_live: float | None = None,
    vpa_live: float | None = None,
) -> tuple[list[dict], bool, str, str]:
    tk = yf.Ticker(f"{ticker}.SA")
    info = tk.info or {}

    det_fund = buscar_detalhes_fundamentus(ticker)
    setor_str = det_fund.get("Setor", "").lower()
    eh_banco_seg = any(k in setor_str for k in ("intermediários financeiros", "bancos", "previdência e seguros"))

    hist_px = tk.history(period="7y", interval="1d", auto_adjust=False)
    if not hist_px.empty:
        hist_px.index = pd.to_datetime(hist_px.index).tz_localize(None)

    acoes_fund = parse_br_num(det_fund.get("Nro. Ações"))
    cot_fund = parse_br_num(det_fund.get("Cotação"))
    val_merc_fd_chk = parse_br_num(det_fund.get("Valor de mercado"))
    if acoes_fund and val_merc_fd_chk and cot_fund and cot_fund > 0:
        acoes_equiv = val_merc_fd_chk / cot_fund
        razao_unit = acoes_fund / acoes_equiv if acoes_equiv > 0 else 1.0
        if 1.8 <= razao_unit <= 10.2 and abs(razao_unit - round(razao_unit)) < 0.15:
            acoes_info = acoes_fund / round(razao_unit)
        else:
            acoes_info = acoes_fund
    elif val_merc_fd_chk and cot_fund and cot_fund > 0:
        acoes_info = val_merc_fd_chk / cot_fund
    else:
        acoes_info = acoes_fund or info.get("sharesOutstanding")

    cot_yf_live = None
    try:
        fi_h = tk.fast_info
        if fi_h:
            cot_yf_live = fi_h.get("lastPrice") or fi_h.get("regularMarketPrice")
    except Exception:
        pass
    cot_atual = cot_live or cot_yf_live or info.get("currentPrice") or info.get("regularMarketPrice") or cot_fund
    if not cot_atual and not hist_px.empty:
        cot_atual = float(hist_px["Close"].iloc[-1])

    # 1) Tenta buscar histórico oficial da CVM (DFP + ITR) em Reais (R$)
    cvm_anuais, cvm_ttm = buscar_dados_cvm_empresa(ticker, det_fund)
    linhas: list[dict] = []
    fonte_anual = "CVM" if cvm_anuais else "Yahoo"
    fin_curr = "BRL"

    if cvm_anuais:
        anos_exibir = sorted(cvm_anuais.keys())[-4:]
        for ano in anos_exibir:
            met = cvm_anuais[ano]
            rec = met.get("rec")
            lbr = met.get("lbr")
            lliq = met.get("lliq")
            patr = met.get("patr")
            div_liq = None if eh_banco_seg else met.get("div_liq")
            ebitda = None if eh_banco_seg else met.get("ebitda")

            px_ano = None
            if not hist_px.empty:
                sub = hist_px[hist_px.index.year == ano]
                if not sub.empty:
                    px_ano = float(sub["Close"].iloc[-1])

            vpa = (patr / acoes_info) if (patr and acoes_info and acoes_info > 0) else None
            val_merc = (px_ano * acoes_info) if (px_ano and acoes_info and acoes_info > 0) else None
            pl = (val_merc / lliq) if (val_merc and lliq and lliq != 0) else None
            pvp = (val_merc / patr) if (val_merc and patr and patr != 0) else None
            pebitda = (val_merc / ebitda) if (not eh_banco_seg and val_merc and ebitda and ebitda != 0) else None
            marg_liq = (lliq / rec * 100.0) if (lliq is not None and rec and rec != 0) else None

            linhas.append({
                "ano": str(ano), "pl": pl, "pvp": pvp, "vpa": vpa, "div_liq": div_liq,
                "marg_liq": marg_liq, "ebitda": ebitda, "pebitda": pebitda,
                "val_merc": val_merc, "lliq": lliq, "lbr": lbr, "rec": rec, "is_atual": False,
            })
    else:
        # Fallback Yahoo Finance com auto-detecção de balanço em USD (mesmo quando info["financialCurrency"] diz "BRL")
        fin = tk.financials
        bal = tk.balance_sheet
        fin_curr = (info.get("financialCurrency") or "BRL").upper()

        if fin_curr == "BRL" and fin is not None and not fin.empty:
            cols_f_chk = sorted(list(fin.columns), key=lambda c: pd.to_datetime(c))
            rec_yf_chk = _pick_row(fin, ["Total Revenue", "Operating Revenue"], cols_f_chk[-1])
            rec_fd_chk = parse_br_num(det_fund.get("Receita Líquida"))
            if rec_yf_chk and rec_fd_chk and 3.5 <= (rec_fd_chk / rec_yf_chk) <= 8.0:
                fin_curr = "USD"
            elif bal is not None and not bal.empty:
                cols_b_chk = sorted(list(bal.columns), key=lambda c: pd.to_datetime(c))
                pl_yf_chk = _pick_row(bal, ["Stockholders Equity", "Total Equity Gross Minority Interest", "Common Stock Equity"], cols_b_chk[-1])
                pl_fd_chk = parse_br_num(det_fund.get("Patrim. Líq"))
                if pl_yf_chk and pl_fd_chk and 3.5 <= (pl_fd_chk / pl_yf_chk) <= 8.0:
                    fin_curr = "USD"

        fx_series = buscar_cambio_brl(fin_curr) if fin_curr != "BRL" else pd.Series(dtype=float)

        if fin is not None and not fin.empty:
            cols_fin = sorted(list(fin.columns), key=lambda c: pd.to_datetime(c))
            cols_bal = list(bal.columns) if (bal is not None and not bal.empty) else []

            for col_f in cols_fin[-4:]:
                ano = pd.to_datetime(col_f).year
                col_b = next((cb for cb in cols_bal if pd.to_datetime(cb).year == ano), None)

                fx_med, fx_fim = 1.0, 1.0
                if fin_curr != "BRL" and not fx_series.empty:
                    sub_fx = fx_series[fx_series.index.year == ano]
                    if not sub_fx.empty:
                        fx_med = float(sub_fx.mean())
                        fx_fim = float(sub_fx.iloc[-1])
                    else:
                        fx_med = float(fx_series.iloc[-1])
                        fx_fim = fx_med

                rec = _pick_row(fin, ["Total Revenue", "Operating Revenue"], col_f)
                lbr = _pick_row(fin, ["Gross Profit"], col_f)
                lliq = _pick_row(fin, ["Net Income", "Net Income Common Stockholders"], col_f)
                ebitda = None
                if not eh_banco_seg:
                    ebitda = _pick_row(fin, ["EBITDA", "Normalized EBITDA"], col_f)
                    if ebitda is None:
                        ebit = _pick_row(fin, ["Operating Income", "EBIT"], col_f)
                        dep = _pick_row(fin, ["Reconciled Depreciation", "Depreciation And Amortization"], col_f)
                        if ebit is not None and dep is not None:
                            ebitda = ebit + dep

                if rec is None and lliq is None and ebitda is None:
                    continue

                if rec is not None:
                    rec *= fx_med
                if lbr is not None:
                    lbr *= fx_med
                if lliq is not None:
                    lliq *= fx_med
                if ebitda is not None:
                    ebitda *= fx_med

                patr = _pick_row(bal, ["Stockholders Equity", "Total Equity Gross Minority Interest", "Common Stock Equity"], col_b) if col_b is not None else None
                if patr is not None:
                    patr *= fx_fim

                div_liq = None
                if not eh_banco_seg and col_b is not None:
                    div_liq = _pick_row(bal, ["Net Debt"], col_b)
                    if div_liq is None:
                        div_tot = _pick_row(bal, ["Total Debt"], col_b)
                        caixa = _pick_row(bal, ["Cash And Cash Equivalents", "Cash Cash Equivalents And Short Term Investments"], col_b)
                        if div_tot is not None and caixa is not None:
                            div_liq = div_tot - caixa
                    if div_liq is not None:
                        div_liq *= fx_fim

                acoes = acoes_fund or (_pick_row(bal, ["Ordinary Shares Number", "Share Issued"], col_b) if col_b is not None else None) or acoes_info
                px_ano = None
                if not hist_px.empty:
                    sub = hist_px[hist_px.index.year == ano]
                    if not sub.empty:
                        px_ano = float(sub["Close"].iloc[-1])

                vpa = (patr / acoes) if (patr and acoes and acoes > 0) else None
                val_merc = (px_ano * acoes) if (px_ano and acoes and acoes > 0) else None
                pl = (val_merc / lliq) if (val_merc and lliq and lliq != 0) else None
                pvp = (val_merc / patr) if (val_merc and patr and patr != 0) else None
                pebitda = (val_merc / ebitda) if (not eh_banco_seg and val_merc and ebitda and ebitda != 0) else None
                marg_liq = (lliq / rec * 100) if (lliq is not None and rec and rec != 0) else None

                linhas.append({
                    "ano": str(ano), "pl": pl, "pvp": pvp, "vpa": vpa, "div_liq": div_liq,
                    "marg_liq": marg_liq, "ebitda": ebitda, "pebitda": pebitda,
                    "val_merc": val_merc, "lliq": lliq, "lbr": lbr, "rec": rec, "is_atual": False,
                })

    # 2) Linha ÚLT. 12M (combina CVM TTM + Fundamentus para precisão máxima em bancos e não bancos)
    fx_atual = 1.0
    if fin_curr != "BRL":
        fx_s = buscar_cambio_brl(fin_curr)
        if not fx_s.empty:
            fx_atual = float(fx_s.iloc[-1])

    rec_fund_12 = parse_br_num(det_fund.get("Receita Líquida"))
    lliq_fund_12 = parse_br_num(det_fund.get("Lucro Líquido"))
    marg_br_pct = parse_br_num(det_fund.get("Marg. Bruta"))
    lbr_fund_12 = (rec_fund_12 * marg_br_pct / 100.0) if (rec_fund_12 is not None and marg_br_pct is not None) else None

    if eh_banco_seg and cvm_ttm:
        rec_12 = cvm_ttm.get("rec") or rec_fund_12
        lbr_12 = cvm_ttm.get("lbr") or lbr_fund_12
        lliq_12 = cvm_ttm.get("lliq") or lliq_fund_12
    else:
        rec_12 = rec_fund_12 or (cvm_ttm.get("rec") if cvm_ttm else None) or (info.get("totalRevenue") * fx_atual if info.get("totalRevenue") else None)
        lbr_12 = lbr_fund_12 or (cvm_ttm.get("lbr") if cvm_ttm else None) or (info.get("grossProfits") * fx_atual if info.get("grossProfits") else None)
        lliq_12 = lliq_fund_12 or (cvm_ttm.get("lliq") if cvm_ttm else None) or (info.get("netIncomeToCommon") * fx_atual if info.get("netIncomeToCommon") else None)

    marg_12 = parse_br_num(det_fund.get("Marg. Líquida"))
    if (marg_12 is None or (eh_banco_seg and marg_12 == 0.0)) and lliq_12 is not None and rec_12 and rec_12 != 0:
        marg_12 = (lliq_12 / rec_12) * 100.0

    val_merc_fund = parse_br_num(det_fund.get("Valor de mercado"))
    val_firma_fund = parse_br_num(det_fund.get("Valor da firma"))
    ev_ebitda_fund = parse_br_num(det_fund.get("EV / EBITDA"))
    div_liq_12 = None if eh_banco_seg else (parse_br_num(det_fund.get("Dív. Líquida")) if det_fund.get("Dív. Líquida") is not None else (cvm_ttm.get("div_liq") if cvm_ttm else None))

    ebitda_12 = None
    if not eh_banco_seg:
        if val_firma_fund and ev_ebitda_fund and ev_ebitda_fund != 0:
            ebitda_12 = val_firma_fund / ev_ebitda_fund
        elif cvm_ttm and cvm_ttm.get("ebitda") is not None:
            ebitda_12 = cvm_ttm.get("ebitda")
        elif info.get("ebitda"):
            ebitda_12 = info.get("ebitda") * fx_atual

    vpa_12 = parse_br_num(det_fund.get("VPA")) or vpa_live
    val_merc_12 = val_merc_fund or ((cot_atual * acoes_info) if (cot_atual and acoes_info) else info.get("marketCap"))
    patr_12 = parse_br_num(det_fund.get("Patrim. Líq")) or ((vpa_12 * acoes_info) if (vpa_12 and acoes_info) else None)
    pl_12 = (val_merc_12 / lliq_12) if (val_merc_12 and lliq_12 and lliq_12 != 0) else (parse_br_num(det_fund.get("P/L")) or pl_live)
    pvp_12 = (val_merc_12 / patr_12) if (val_merc_12 and patr_12 and patr_12 != 0) else (parse_br_num(det_fund.get("P/VP")) or pvp_live)
    pebitda_12 = (val_merc_12 / ebitda_12) if (not eh_banco_seg and val_merc_12 and ebitda_12 and ebitda_12 != 0) else None

    linhas.append({
        "ano": "ÚLT. 12M", "pl": pl_12, "pvp": pvp_12, "vpa": vpa_12, "div_liq": div_liq_12,
        "marg_liq": marg_12, "ebitda": ebitda_12, "pebitda": pebitda_12,
        "val_merc": val_merc_12, "lliq": lliq_12, "lbr": lbr_12, "rec": rec_12, "is_atual": False,
    })

    # 3) Linha ATUAL (recalculada pela cotação vigente)
    cot_txt = f" (R$ {fmt_num(cot_atual)})" if cot_atual else ""
    val_merc_atual = ((cot_atual * acoes_info) if (cot_atual and acoes_info) else val_merc_12)
    pl_atual = (val_merc_atual / lliq_12) if (val_merc_atual and lliq_12 and lliq_12 != 0) else (pl_live if pl_live is not None else pl_12)
    patr_atual = parse_br_num(det_fund.get("Patrim. Líq")) or ((vpa_12 * acoes_info) if (vpa_12 and acoes_info) else None)
    pvp_atual = (val_merc_atual / patr_atual) if (val_merc_atual and patr_atual and patr_atual != 0) else (pvp_live if pvp_live is not None else pvp_12)
    pebitda_atual = (val_merc_atual / ebitda_12) if (not eh_banco_seg and val_merc_atual and ebitda_12 and ebitda_12 != 0) else pebitda_12

    # 2.5) Linha MÉDIA (anos inteiros + meses inéditos do ano atual, sem repetir meses do ano anterior em ÚLT. 12M)
    linhas_anuais = [x for x in linhas if x["ano"] != "ÚLT. 12M"]
    linha_12m = next((x for x in linhas if x["ano"] == "ÚLT. 12M"), None)
    if linhas_anuais:
        ult_ano_dfp = max(int(x["ano"]) for x in linhas_anuais)
        mes_atual_bal = 0
        ano_bal = ult_ano_dfp
        if cvm_ttm and cvm_ttm.get("dt_ref"):
            try:
                dt_parts = str(cvm_ttm["dt_ref"]).split("-")
                ano_bal = int(dt_parts[0])
                mes_atual_bal = int(dt_parts[1])
            except Exception:
                pass
        if ano_bal <= ult_ano_dfp:
            dt_ult_str = (det_fund.get("Últ balanço processado") or "").strip()
            m_dt = re.match(r"^\d{2}/(\d{2})/(\d{4})$", dt_ult_str)
            if m_dt:
                mes_f, ano_f = int(m_dt.group(1)), int(m_dt.group(2))
                if ano_f > ult_ano_dfp:
                    ano_bal, mes_atual_bal = ano_f, mes_f

        meses_novos = mes_atual_bal if (ano_bal > ult_ano_dfp and 1 <= mes_atual_bal <= 12) else 0
        total_meses = len(linhas_anuais) * 12 + meses_novos
        total_anos_eq = total_meses / 12.0

        def _media_ponderada_meses(campo: str) -> float | None:
            pares = [(float(x[campo]), 12) for x in linhas_anuais if x.get(campo) is not None]
            if meses_novos > 0 and linha_12m and linha_12m.get(campo) is not None:
                pares.append((float(linha_12m[campo]), meses_novos))
            if not pares:
                return None
            soma_p = sum(p for _, p in pares)
            return sum(v * p for v, p in pares) / soma_p if soma_p > 0 else None

        def _media_fluxo_anualizado(campo: str, ytd_key: str | None) -> float | None:
            vals_dfp = [float(x[campo]) for x in linhas_anuais if x.get(campo) is not None]
            if len(vals_dfp) != len(linhas_anuais) or not vals_dfp:
                return _media_ponderada_meses(campo)
            soma_total = sum(vals_dfp)
            if meses_novos == 0:
                return soma_total / len(vals_dfp)
            ytd_val = cvm_ttm.get(ytd_key) if (cvm_ttm and ytd_key) else None
            if ytd_val is not None:
                return (soma_total + float(ytd_val)) / total_anos_eq
            val_12m = linha_12m.get(campo) if linha_12m else None
            val_ult_dfp = next((x.get(campo) for x in linhas_anuais if int(x["ano"]) == ult_ano_dfp), None)
            if val_12m is not None and val_ult_dfp is not None:
                frac_rep = (12 - meses_novos) / 12.0
                return (soma_total + float(val_12m) - frac_rep * float(val_ult_dfp)) / total_anos_eq
            return soma_total / len(vals_dfp)

        rec_med = _media_fluxo_anualizado("rec", "ytd_rec")
        lbr_med = _media_fluxo_anualizado("lbr", "ytd_lbr")
        lliq_med = _media_fluxo_anualizado("lliq", "ytd_lliq")
        ebitda_med = None if eh_banco_seg else _media_fluxo_anualizado("ebitda", "ytd_ebitda")
        if lliq_med is not None and rec_med and rec_med != 0:
            marg_med = (lliq_med / rec_med) * 100.0
        else:
            marg_med = _media_ponderada_meses("marg_liq")

        if meses_novos > 0:
            media_info = (
                f" Linha MÉDIA: {len(linhas_anuais)} ano(s) completo(s) + {meses_novos} meses de {ano_bal} "
                f"(descontando os {12 - meses_novos} meses de {ult_ano_dfp} presentes em ÚLT. 12M)."
            )
        else:
            media_info = f" Linha MÉDIA: média dos {len(linhas_anuais)} ano(s) completo(s) acima."

        linhas.append({
            "ano": "MÉDIA",
            "pl": _media_ponderada_meses("pl"),
            "pvp": _media_ponderada_meses("pvp"),
            "vpa": _media_ponderada_meses("vpa"),
            "div_liq": None if eh_banco_seg else _media_ponderada_meses("div_liq"),
            "marg_liq": marg_med,
            "ebitda": ebitda_med,
            "pebitda": None if eh_banco_seg else _media_ponderada_meses("pebitda"),
            "val_merc": _media_ponderada_meses("val_merc"),
            "lliq": lliq_med,
            "lbr": lbr_med,
            "rec": rec_med,
            "is_atual": False,
            "is_media": True,
            "media_info": media_info,
        })

    linhas.append({
        "ano": f"ATUAL{cot_txt}",
        "pl": pl_atual,
        "pvp": pvp_atual,
        "vpa": vpa_12 if vpa_12 is not None else vpa_live,
        "div_liq": div_liq_12, "marg_liq": marg_12, "ebitda": ebitda_12,
        "pebitda": pebitda_atual, "val_merc": val_merc_atual,
        "lliq": lliq_12, "lbr": lbr_12, "rec": rec_12, "is_atual": True,
    })

    return linhas, eh_banco_seg, fin_curr, fonte_anual


def toggle_favorito(ticker: str):
    favs = list(st.session_state["favoritos"])
    if ticker in favs:
        favs.remove(ticker)
    else:
        favs.append(ticker)
    st.session_state["favoritos"] = favs
    st.session_state["ms_favs"] = favs
    salvar_dados_usuario_nuvem()


def badge_veredito_html(veredito: str) -> str:
    estilos = {
        "🟢 Excelente": ("rgba(34,197,94,0.18)", "#22c55e", "rgba(34,197,94,0.45)", "🟢 Excelente"),
        "🔵 Bom": ("rgba(59,130,246,0.18)", "#60a5fa", "rgba(59,130,246,0.45)", "🔵 Bom (LP)"),
        "🟣 Esticado": ("rgba(168,85,247,0.18)", "#c084fc", "rgba(168,85,247,0.45)", "🟣 Esticado"),
        "🟠 Indeciso": ("rgba(249,115,22,0.18)", "#fb923c", "rgba(249,115,22,0.45)", "🟠 Indeciso"),
        "🟡 Regular": ("rgba(234,179,8,0.18)", "#facc15", "rgba(234,179,8,0.45)", "🟡 Regular"),
        "🔴 Crítico": ("rgba(239,68,68,0.18)", "#f87171", "rgba(239,68,68,0.45)", "🔴 Crítico"),
    }
    bg, fg, bd, lbl = ("rgba(148,163,184,0.18)", "#94a3b8", "rgba(148,163,184,0.4)", veredito)
    for pref, cfg in estilos.items():
        if veredito.startswith(pref):
            bg, fg, bd, lbl = cfg
            break
    return (
        f"<span title='{html.escape(veredito)}' style='display:inline-block; padding:1px 6px; "
        f"border-radius:10px; font-size:11px; font-weight:700; background:{bg}; color:{fg}; "
        f"border:1px solid {bd}; white-space:nowrap; margin:2px 0;'>{html.escape(lbl)}</span>"
    )


def fmt_faixa_preco_modelo(r: dict) -> str:
    teto_m = r.get("preco_teto_modelo")
    sobre_m = r.get("preco_sobrepreco")
    p1 = f"Teto com margem até **R$ {fmt_num(teto_m)}**" if (teto_m and teto_m > 0) else "Teto com margem: **—**"
    p2 = f"Zona de Sobrepreço acima de **R$ {fmt_num(sobre_m)}**" if (sobre_m and sobre_m > 0) else "Zona de Sobrepreço: **—**"
    return f"{p1} | {p2}"


def render_grafico_e_tabela_ativo(
    ticker: str,
    nome: str = "",
    base_ativo: dict | None = None,
    key_prefix: str = "raiox",
    modo_score_chave: str = "score_geral",
):
    c_tit, c_fav = st.columns([4, 1.3])
    eh_fav = ticker in st.session_state["favoritos"]
    with c_tit:
        st.markdown(f"### 📈 COTAÇÃO {ticker} {f'— {nome}' if nome and nome != ticker else ''}")
    with c_fav:
        lbl_fav = "★ Remover dos Favoritos" if eh_fav else "⭐ Adicionar aos Favoritos"
        if st.button(lbl_fav, key=f"{key_prefix}_favbtn_{ticker}", use_container_width=True):
            toggle_favorito(ticker)
            st.rerun(scope="app")

    if base_ativo and "veredito" in base_ativo:
        pos_r = base_ativo.get("pos_ranking", "-")
        cot_r = float(base_ativo.get("cotacao") or 0.0)
        score_at_r = base_ativo.get("score_ativo", base_ativo.get(modo_score_chave, base_ativo.get("score_geral", 0.0)))
        score_lp_r = base_ativo.get("score_lp", 0.0)
        score_cp_r = base_ativo.get("score_cp", 0.0)
        news_sc_r = float(base_ativo.get("news_score") or 0.0)
        news_res_r = base_ativo.get("news_resumo", "⚪ Neutro")
        veredito_r = base_ativo.get("veredito", "🟡 Regular (Neutro)")
        ifr_r = base_ativo.get("ifr_14")
        dist_200_r = base_ativo.get("dist_mm200_pct")
        dist_52_r = base_ativo.get("dist_max_52s_pct")
        motivos_r = base_ativo.get("motivos", [])
        just_r = "; ".join(motivos_r).capitalize() + "." if motivos_r else "Sem dados suficientes."
        ifr_txt_r = fmt_num(ifr_r, 1) if ifr_r is not None else "—"
        d200_txt_r = f"{dist_200_r:+.1f}%" if dist_200_r is not None else "—"
        d52_txt_r = f"{dist_52_r:+.1f}%" if dist_52_r is not None else "—"

        with st.container(border=True):
            st.markdown(
                f"**{pos_r}º Lugar — {ticker}** ({nome or ticker}) | "
                f"Cotação: **R$ {fmt_num(cot_r)}** | "
                f"Score Ativo: **{score_at_r}/100** "
                f"(LP: **{score_lp_r}** | CP: **{score_cp_r}** | News: **{news_sc_r:+.1f}**) | {veredito_r}"
            )
            rx_m1, rx_m2, rx_m3, rx_m4 = st.columns(4)
            rx_m1.metric("🏛️ Longo Prazo (LP)", f"{score_lp_r}/100")
            rx_m2.metric("⚡ Curto Prazo (CP)", f"{score_cp_r}/100")
            rx_m3.metric("📰 Notícias (30d)", f"{news_sc_r:+.1f}", news_res_r)
            rx_m4.metric("📊 IFR (14d)", ifr_txt_r, f"MM200: {d200_txt_r} | 52s: {d52_txt_r}")
            st.markdown(f"🎯 **Faixa de Preço do Modelo:** {fmt_faixa_preco_modelo(base_ativo)}")
            st.markdown(f"📝 **Justificativa:** _{just_r}_")

    c_per, c_tipo = st.columns([3, 1.2])
    with c_per:
        periodo = st.radio(
            "Período:",
            ["1 D", "7 D", "30 D", "6 M", "YTD", "1 A", "5 A", "10 A", "15 A"],
            index=5, horizontal=True, key=f"{key_prefix}_per_{ticker}",
        )
    with c_tipo:
        tipo_cot = st.selectbox(
            "Tipo:", ["Cotação ajustada", "Cotação simples"],
            index=0, key=f"{key_prefix}_tipo_{ticker}",
        )

    ajustada = tipo_cot == "Cotação ajustada"
    serie = buscar_historico_preco(ticker, periodo, ajustada)

    if serie.empty:
        st.warning(f"Não foi possível carregar o gráfico de {ticker} para o período {periodo}.")
    else:
        p_ini, p_fim = float(serie.iloc[0]), float(serie.iloc[-1])
        var_pct = ((p_fim - p_ini) / p_ini) * 100 if p_ini > 0 else 0.0
        cor = "#22c55e" if var_pct >= 0 else "#ef4444"
        fill_cor = "rgba(34, 197, 94, 0.22)" if var_pct >= 0 else "rgba(239, 68, 68, 0.22)"
        sinal = "+" if var_pct >= 0 else ""

        st.markdown(
            f"<div style='font-size:26px; font-weight:700; margin-bottom:4px;'>"
            f"R$ {fmt_num(p_fim)} "
            f"<span style='font-size:16px; color:{cor}; font-weight:600;'>{sinal}{fmt_num(var_pct)}% ({periodo})</span>"
            f"</div>",
            unsafe_allow_html=True,
        )

        fig = go.Figure()
        fmt_hover = "%{x|%d/%m/%Y %H:%M}" if periodo in ("1 D", "7 D") else "%{x|%d/%m/%Y}"
        fig.add_trace(
            go.Scatter(
                x=serie.index, y=serie.values, mode="lines",
                line=dict(color=cor, width=2.2), fill="tozeroy", fillcolor=fill_cor,
                hovertemplate=f"{fmt_hover}<br><b>R$ %{{y:.2f}}</b><extra></extra>",
            )
        )
        y_min, y_max = float(serie.min()), float(serie.max())
        margem_y = (y_max - y_min) * 0.08 if y_max > y_min else y_max * 0.05
        fig.update_layout(
            height=320, margin=dict(l=10, r=65, t=15, b=15),
            paper_bgcolor="rgba(0,0,0,0)", plot_bgcolor="rgba(0,0,0,0)",
            showlegend=False, hovermode="x unified",
            xaxis=dict(showgrid=False, zeroline=False),
            yaxis=dict(showgrid=True, gridcolor="rgba(128,128,128,0.25)", tickprefix="R$ ", range=[max(0, y_min - margem_y), y_max + margem_y]),
            annotations=[
                dict(xref="paper", x=1.01, y=p_fim, xanchor="left", yanchor="middle",
                     text=f"<b>{fmt_num(p_fim)}</b>", showarrow=False,
                     font=dict(color="white", size=12), bgcolor=cor, borderpad=4)
            ],
        )
        st.plotly_chart(fig, use_container_width=True, key=f"{key_prefix}_plot_{ticker}")

        serie_max = buscar_serie_max_ajustada(ticker)
        if not serie_max.empty:
            s1, s2, s3 = st.columns([1.4, 1.2, 2.2])
            with s1:
                valor_inv = st.number_input("Se você tivesse investido (R$):", min_value=10.0, value=1000.0, step=100.0, key=f"{key_prefix}_val_{ticker}")
            with s2:
                janela_sim = st.selectbox("Há:", ["1 mês", "6 meses", "1 ano", "5 anos", "10 anos", "15 anos"], index=2, key=f"{key_prefix}_jan_{ticker}")
            deltas = {
                "1 mês": pd.DateOffset(months=1), "6 meses": pd.DateOffset(months=6),
                "1 ano": pd.DateOffset(years=1), "5 anos": pd.DateOffset(years=5),
                "10 anos": pd.DateOffset(years=10), "15 anos": pd.DateOffset(years=15),
            }
            data_alvo = serie_max.index.max() - deltas[janela_sim]
            recorte = serie_max[serie_max.index >= data_alvo]
            p_base = float(recorte.iloc[0]) if not recorte.empty else float(serie_max.iloc[0])
            p_hoje = float(serie_max.iloc[-1])
            valor_hoje = valor_inv * (p_hoje / p_base) if p_base > 0 else valor_inv
            cor_sim = "#22c55e" if valor_hoje >= valor_inv else "#ef4444"
            data_efetiva = recorte.index[0].strftime("%d/%m/%Y") if not recorte.empty else serie_max.index[0].strftime("%d/%m/%Y")
            with s3:
                st.markdown(
                    f"<div style='padding-top:26px; font-size:17px;'>"
                    f"hoje você teria <strong style='color:{cor_sim}; font-size:20px;'>R$ {fmt_num(valor_hoje)}</strong>"
                    f"<br><small style='opacity:0.7;'>*Desde {data_efetiva}, considerando reinvestimento dos dividendos.</small>"
                    f"</div>",
                    unsafe_allow_html=True,
                )

    st.markdown(f"#### 📑 Histórico Fundamentalista — {ticker}")
    with st.spinner(f"Carregando balanços oficiais da CVM (DFP/ITR) para {ticker}..."):
        hist_fund, eh_banco, fin_curr, fonte_anual = buscar_historico_fundamentalista(
            ticker,
            cot_live=base_ativo.get("cotacao") if base_ativo else None,
            pl_live=base_ativo.get("pl") if base_ativo else None,
            pvp_live=base_ativo.get("pvp") if base_ativo else None,
            vpa_live=base_ativo.get("vpa") if base_ativo else None,
        )
    if not hist_fund:
        st.info("Histórico anual detalhado indisponível para este ativo.")
    else:
        rows_h = []
        media_info_txt = ""
        for h in hist_fund:
            pl_s = fmt_num(h["pl"]) if h["pl"] is not None else "—"
            pvp_s = fmt_num(h["pvp"]) if h["pvp"] is not None else "—"
            vpa_s = fmt_num(h["vpa"]) if h["vpa"] is not None else "—"
            ml_s = f"{fmt_num(h['marg_liq'])}%" if h["marg_liq"] is not None else "—"
            peb_s = fmt_num(h["pebitda"]) if h["pebitda"] is not None else "—"
            if h.get("is_atual"):
                estilo_row = "background-color:rgba(96,165,250,0.14); font-weight:700;"
            elif h.get("is_media"):
                estilo_row = "background-color:rgba(250,204,21,0.12); font-weight:700; border-top:1px dashed rgba(250,204,21,0.45);"
                media_info_txt = h.get("media_info", "")
            else:
                estilo_row = ""
            rows_h.append(
                f"<tr style='{estilo_row}'>"
                f"<td style='font-weight:700;'>{html.escape(h['ano'])}</td>"
                f"<td>{pl_s}</td><td>{pvp_s}</td><td>{vpa_s}</td>"
                f"<td>{fmt_bi_mi(h['div_liq'])}</td><td>{ml_s}</td>"
                f"<td>{fmt_bi_mi(h['ebitda'])}</td><td>{peb_s}</td>"
                f"<td>{fmt_bi_mi(h['val_merc'])}</td><td>{fmt_bi_mi(h['lliq'])}</td>"
                f"<td>{fmt_bi_mi(h['lbr'])}</td><td>{fmt_bi_mi(h['rec'])}</td>"
                "</tr>"
            )

        css_h = (
            "<style>"
            ".hist-wrap{width:100%;overflow-x:auto;}"
            ".hist-table{width:100%;border-collapse:collapse;font-size:13px;text-align:center;}"
            ".hist-table th{background-color:rgba(128,128,128,0.18);padding:10px 8px;border-bottom:2px solid rgba(128,128,128,0.35);font-weight:600;white-space:nowrap;}"
            ".hist-table td{padding:9px 8px;border-bottom:1px solid rgba(128,128,128,0.2);white-space:nowrap;}"
            ".hist-table tr:hover td{background-color:rgba(128,128,128,0.08);}"
            "</style>"
        )
        html_h = (
            f"{css_h}<div class='hist-wrap'><table class='hist-table'><thead><tr>"
            "<th>Ano</th><th>P/L</th><th>P/VP</th><th>VPA</th><th>Dívida líquida</th>"
            "<th>Margem líquida</th><th>EBITDA</th><th>P/EBITDA</th><th>Valor de mercado</th>"
            "<th>Lucro Líq.</th><th>Lucro Br.</th><th>Receita Líq.</th>"
            f"</tr></thead><tbody>{''.join(rows_h)}</tbody></table></div>"
        )
        st.markdown(html_h, unsafe_allow_html=True)
        if fonte_anual == "CVM":
            nota_src = "Dados anuais oficiais da CVM (DFP/ITR) em R$, com VPA e Valor de mercado históricos ajustados por desdobramentos."
        else:
            nota_fx = f" Balanço anual reportado em {fin_curr} convertido para R$ pelo câmbio histórico." if fin_curr != "BRL" else ""
            nota_src = f"VPA histórico ajustado por desdobramentos.{nota_fx}"
        nota_b = " Para bancos/seguradoras, Dívida Líquida e EBITDA não se aplicam (`—`)." if eh_banco else ""
        st.caption(f"Nota: {nota_src}{media_info_txt}{nota_b}")


def calc_ms(preco_calc: float | None, cotacao: float) -> float | None:
    if preco_calc is None or preco_calc <= 0:
        return None
    return ((preco_calc - cotacao) / preco_calc) * 100


def html_preco_ms(preco_calc: float | None, cotacao: float, sufixo: str = "") -> str:
    if preco_calc is None or preco_calc <= 0:
        return "<span style='opacity:0.55;'>—</span>"
    ms = calc_ms(preco_calc, cotacao)
    sinal = "+" if ms >= 0 else ""
    if cotacao <= preco_calc:
        cor, status = "#22c55e", "🟢 (abaixo)"
    else:
        cor, status = "#ef4444", "🔴 (acima)"
    return (
        f"<strong>R$ {fmt_num(preco_calc)}{sufixo}</strong><br>"
        f"<span style='color:{cor}; font-weight:600; white-space:nowrap;'>"
        f"{sinal}{fmt_num(ms, 1)}% {status}</span>"
    )


def calcular_score(d: dict, pt_med: float | None, pt_proj: float | None, pt_bazin: float | None, graham: float | None) -> dict:
    cot = float(d.get("cotacao") or 0.0)
    eh_banco_seg = bool(d.get("eh_banco_seg", False))

    pl = d.get("pl")
    pvp = d.get("pvp")
    roe = d.get("roe")
    roic = d.get("roic")
    marg_liq = d.get("marg_liq")
    marg_ebit = d.get("marg_ebit")
    ev_ebitda = d.get("ev_ebitda")
    liq_corr = d.get("liq_corr")
    div_brut_patrim = d.get("div_brut_patrim")
    cresc_rec_5a = d.get("cresc_rec_5a")

    dy_12m = float(d.get("dy_12m") or 0.0)
    dpa_med_6a = float(d.get("dpa_med_6a") or 0.0)
    anos_hist = int(d.get("anos_hist") or 0)

    ifr_14 = d.get("ifr_14")
    mm20 = d.get("mm20")
    mm50 = d.get("mm50")
    mm200 = d.get("mm200")
    dist_mm50_pct = d.get("dist_mm50_pct")
    dist_mm200_pct = d.get("dist_mm200_pct")
    dist_max_52s_pct = d.get("dist_max_52s_pct")
    razao_volume = d.get("razao_volume")

    news_score = float(d.get("news_score") or 0.0)
    news_resumo = str(d.get("news_resumo") or "⚪ Neutro")

    # === 1) FAIXAS DE PREÇO DO MODELO (CVM COMPLIANT) ===
    div_teto_ref = pt_med if (pt_med and pt_med > 0) else (pt_bazin if (pt_bazin and pt_bazin > 0) else None)
    cands_teto = []
    if graham and graham > 0:
        cands_teto.append(float(graham))
    if div_teto_ref and div_teto_ref > 0:
        cands_teto.append(float(div_teto_ref) * 0.85)
    preco_teto_modelo = min(cands_teto) if cands_teto else None

    dpa_ref_sp = d.get("dpa_proj") if (d.get("dpa_proj") and d.get("dpa_proj") > 0) else (d.get("dpa_12m") if (d.get("dpa_12m") and d.get("dpa_12m") > 0) else None)
    p_yield_4pct = (float(dpa_ref_sp) / 0.04) if (dpa_ref_sp and dpa_ref_sp > 0) else None
    p_graham_125 = (float(graham) * 1.25) if (graham and graham > 0) else None
    cands_sp = [x for x in (p_yield_4pct, p_graham_125) if x is not None]
    preco_sobrepreco = max(cands_sp) if cands_sp else None

    # === 2) SCORE LONGO PRAZO (0 a 100) ===
    # 2.1 Valuation com Fator de Confiança (35 pts)
    ms_lista = [x for x in [calc_ms(pt_med, cot), calc_ms(pt_proj, cot), calc_ms(pt_bazin, cot), calc_ms(graham, cot)] if x is not None]
    n_metodos = len(ms_lista)
    if n_metodos == 1:
        fator_confianca = 0.60
    elif n_metodos == 2:
        fator_confianca = 0.85
    else:
        fator_confianca = 1.0

    if ms_lista:
        ms_limitadas = [max(-40.0, min(60.0, m)) for m in ms_lista]
        avg_ms_lim = sum(ms_limitadas) / n_metodos
        avg_ms_real = sum(ms_lista) / n_metodos
        pts_ms = max(0.0, min(20.0, ((avg_ms_lim + 40.0) / 100.0) * 20.0)) * fator_confianca
    else:
        avg_ms_real = None
        pts_ms = 0.0

    pts_pvp_m = (max(0.0, min(3.0, ((2.5 - pvp) / 1.5) * 3.0)) + (1.0 if pvp < 1.0 else 0.0)) if (pvp and pvp > 0) else 0.0
    pts_pl_m = max(0.0, min(4.0, ((20.0 - pl) / 15.0) * 4.0)) if (pl and pl > 0) else 0.0
    if eh_banco_seg:
        pts_mult = (pts_pvp_m + pts_pl_m) * (10.0 / 8.0)
    else:
        pts_ev = max(0.0, min(2.0, ((12.0 - ev_ebitda) / 8.0) * 2.0)) if (ev_ebitda and ev_ebitda > 0) else 0.0
        pts_mult = pts_pvp_m + pts_pl_m + pts_ev

    if dy_12m <= 0.0 and dpa_med_6a <= 0.0 and anos_hist <= 0:
        pts_div = 0.0
    else:
        pts_dy12 = min(3.5, (max(0.0, dy_12m) / 8.0) * 3.5)
        pts_h6 = min(1.5, (min(anos_hist, 6) / 6.0) * 1.5) if anos_hist > 0 else 0.0
        pts_div = min(5.0, pts_dy12 + pts_h6)

    pts_val_lp = min(35.0, pts_ms + pts_mult + pts_div)

    # 2.2 Rentabilidade / ROE / ROIC / Margem (30 pts)
    if eh_banco_seg:
        pts_roe_lp = min(20.0, (roe / 22.0) * 20.0) if (roe and roe > 0) else 0.0
        if marg_liq is not None:
            pts_marg_lp = min(10.0, (marg_liq / 20.0) * 10.0) if marg_liq > 0 else 0.0
        else:
            pts_marg_lp = 5.0 if (roe and roe >= 12.0) else 0.0
        pts_rent_lp = min(30.0, pts_roe_lp + pts_marg_lp)
    else:
        pts_roe_lp = min(12.0, (roe / 25.0) * 12.0) if (roe and roe > 0) else 0.0
        if roic is not None:
            pts_roic_lp = min(10.0, (roic / 20.0) * 10.0) if roic > 0 else 0.0
        else:
            pts_roic_lp = min(10.0, (roe / 25.0) * 10.0) if (roe and roe > 0) else 0.0
        pts_ml_lp = min(5.0, (marg_liq / 20.0) * 5.0) if (marg_liq and marg_liq > 0) else 0.0
        if marg_ebit is not None:
            pts_me_lp = min(3.0, (marg_ebit / 25.0) * 3.0) if marg_ebit > 0 else 0.0
        else:
            pts_me_lp = min(3.0, (marg_liq / 20.0) * 3.0) if (marg_liq and marg_liq > 0) else 0.0
        pts_rent_lp = min(30.0, pts_roe_lp + pts_roic_lp + pts_ml_lp + pts_me_lp)

    # 2.3 Saúde Financeira: Dívida / Liquidez / Crescimento (25 pts)
    if eh_banco_seg:
        if roe is not None and roe >= 15.0 and (pl is None or pl > 0):
            pts_solv = 15.0
        elif roe is not None and roe >= 10.0 and (pl is None or pl > 0):
            pts_solv = 12.0
        elif roe is not None and roe > 0:
            pts_solv = 8.0
        else:
            pts_solv = 2.0
        pts_cresc = max(0.0, min(10.0, ((cresc_rec_5a + 5.0) / 20.0) * 10.0)) if (cresc_rec_5a is not None) else 4.0
        pts_saude_lp = min(25.0, pts_solv + pts_cresc)
    else:
        if div_brut_patrim is not None:
            if div_brut_patrim <= 0.5:
                pts_divida = 10.0
            elif div_brut_patrim <= 3.0:
                pts_divida = max(0.0, 10.0 - ((div_brut_patrim - 0.5) / 2.5) * 10.0)
            else:
                pts_divida = 0.0
        else:
            pts_divida = 5.0

        if liq_corr is not None:
            if liq_corr >= 1.5:
                pts_liq = 7.0
            elif liq_corr >= 0.8:
                pts_liq = ((liq_corr - 0.8) / 0.7) * 7.0
            else:
                pts_liq = 0.0
        else:
            pts_liq = 3.5

        pts_cresc = max(0.0, min(8.0, ((cresc_rec_5a + 5.0) / 20.0) * 8.0)) if (cresc_rec_5a is not None) else 3.0
        pts_saude_lp = min(25.0, pts_divida + pts_liq + pts_cresc)

    # 2.4 Contexto Notícias LP (10 pts)
    pts_news_lp = max(0.0, min(10.0, ((news_score + 10.0) / 20.0) * 10.0))

    score_lp_bruto = pts_val_lp + pts_rent_lp + pts_saude_lp + pts_news_lp

    # Trava Anti-Armadilha (Value Trap)
    armadilha_motivos = []
    if marg_liq is not None and marg_liq < 0:
        armadilha_motivos.append(f"margem líquida negativa ({fmt_num(marg_liq, 1)}%)")
    if roe is not None and roe < 0:
        armadilha_motivos.append(f"ROE negativo ({fmt_num(roe, 1)}%)")
    if (not eh_banco_seg) and (div_brut_patrim is not None) and div_brut_patrim > 3.0:
        armadilha_motivos.append(f"Dív/Patrim elevada ({fmt_num(div_brut_patrim)}x > 3,0x)")
    if "🚨" in news_resumo:
        armadilha_motivos.append("risco crítico em notícias (RJ/fraude/alerta)")

    eh_value_trap = len(armadilha_motivos) > 0
    score_lp = round(min(score_lp_bruto, 50.0) if eh_value_trap else min(100.0, score_lp_bruto), 1)

    # === 3) SCORE CURTO PRAZO (0 a 100) ===
    # 3.1 Ponto Técnico / IFR 14 sob-vendido entre 30 e 48 (40 pts)
    if ifr_14 is not None:
        if 30.0 <= ifr_14 <= 48.0:
            pts_ifr = 40.0 - (abs(ifr_14 - 38.0) / 10.0) * 4.0
        elif ifr_14 < 30.0:
            pts_ifr = max(18.0, 35.0 - (30.0 - ifr_14))
        elif ifr_14 <= 65.0:
            pts_ifr = max(16.0, 35.0 - ((ifr_14 - 48.0) / 17.0) * 19.0)
        else:
            pts_ifr = max(0.0, 16.0 - ((ifr_14 - 65.0) / 20.0) * 16.0)
    else:
        pts_ifr = 20.0

    # 3.2 Médias MM20 / MM50 / MM200 e Máx 52s (25 pts)
    if mm20 is None and mm50 is None and mm200 is None:
        pts_medias = 12.5
    else:
        pts_mm200 = 3.0
        if dist_mm200_pct is not None:
            if 0.0 <= dist_mm200_pct <= 25.0:
                pts_mm200 = 6.0
            elif -12.0 <= dist_mm200_pct < 0.0:
                pts_mm200 = 4.0
            elif dist_mm200_pct > 25.0:
                pts_mm200 = 2.0
            else:
                pts_mm200 = 1.0

        pts_mm50 = 2.5
        if dist_mm50_pct is not None:
            if -6.0 <= dist_mm50_pct <= 6.0:
                pts_mm50 = 5.0
            elif 6.0 < dist_mm50_pct <= 15.0 or -12.0 <= dist_mm50_pct < -6.0:
                pts_mm50 = 3.0
            else:
                pts_mm50 = 1.0

        pts_mm20 = 2.0
        if mm20 is not None and cot > 0:
            if cot >= mm20 and (mm50 is None or mm20 >= mm50):
                pts_mm20 = 4.0
            elif cot >= mm20 or abs((cot / mm20) - 1.0) <= 0.03:
                pts_mm20 = 3.0
            else:
                pts_mm20 = 1.0

        if dist_max_52s_pct is not None:
            if -25.0 <= dist_max_52s_pct <= -5.0:
                pts_52s = 10.0
            elif dist_max_52s_pct > -5.0:
                pts_52s = 6.0
            elif dist_max_52s_pct >= -40.0:
                pts_52s = 6.0
            else:
                pts_52s = 2.0
        else:
            pts_52s = 5.0

        pts_medias = min(25.0, pts_mm200 + pts_mm50 + pts_mm20 + pts_52s)

    # 3.3 Catalisadores / News Score CP (25 pts)
    pts_news_cp = max(0.0, min(25.0, ((news_score + 10.0) / 20.0) * 25.0))

    # 3.4 Volume Comprador (10 pts)
    if razao_volume is not None:
        pts_vol = max(2.0, min(10.0, (razao_volume / 1.5) * 10.0))
        em_distribuicao = (mm20 is not None and cot > 0 and cot < mm20 * 0.97 and news_score < 0)
        if em_distribuicao:
            pts_vol = min(pts_vol, 5.0)
    else:
        pts_vol = 5.0

    score_cp = round(min(100.0, pts_ifr + pts_medias + pts_news_cp + pts_vol), 1)
    score_geral = round((0.60 * score_lp) + (0.40 * score_cp), 1)

    # === 4) VEREDITO QUANTITATIVO DO MODELO (6 SELOS) ===
    esta_esticado = (
        (preco_sobrepreco is not None and cot > 0 and cot >= preco_sobrepreco)
        or (avg_ms_real is not None and avg_ms_real < -15.0)
        or (ifr_14 is not None and ifr_14 >= 72.0 and (avg_ms_real is None or avg_ms_real < 5.0))
        or (dist_mm200_pct is not None and dist_mm200_pct > 30.0 and (avg_ms_real is None or avg_ms_real < 0.0))
    )

    if eh_value_trap or score_lp < 38.0 or (score_geral < 42.0 and not esta_esticado):
        veredito = "🔴 Crítico (Risco Alto)"
    elif esta_esticado:
        veredito = "🟣 Esticado (Alerta Topo/Sobrepreço)"
    elif score_geral >= 72.0 and score_lp >= 70.0 and (avg_ms_real is None or avg_ms_real > 0.0):
        veredito = "🟢 Excelente (Forte Atratividade)"
    elif score_lp >= 62.0 and score_geral >= 58.0:
        veredito = "🔵 Bom (Acúmulo LP)"
    elif abs(score_lp - score_cp) >= 20.0 or (score_lp >= 58.0 and news_score <= -2.5) or (score_cp >= 65.0 and score_lp < 55.0):
        veredito = "🟠 Indeciso (Sinais Mistos)"
    else:
        veredito = "🟡 Regular (Neutro)"

    # === 5) MOTIVOS EXPLICATIVOS ===
    motivos = []
    if eh_value_trap:
        motivos.append(f"⚠️ Trava Anti-Armadilha (teto LP 50): {', '.join(armadilha_motivos)}")
    if avg_ms_real is not None:
        if avg_ms_real > 15:
            motivos.append(f"forte desconto médio ({avg_ms_real:+.1f}%) nos métodos")
        elif avg_ms_real > 0:
            motivos.append(f"margem de segurança média positiva ({avg_ms_real:+.1f}%)")
        else:
            motivos.append(f"negociada acima da média dos preços-teto ({avg_ms_real:+.1f}%)")
    if n_metodos == 1:
        motivos.append("cobertura limitada (apenas 1 método; trava -40%)")
    elif n_metodos == 2:
        motivos.append("cobertura parcial (2 métodos; trava -15%)")
    if dy_12m <= 0.0 and dpa_med_6a <= 0.0 and anos_hist <= 0:
        motivos.append("sem histórico de dividendos (DY 0%)")
    elif dy_12m >= 6.0:
        motivos.append(f"DY atrativo ({fmt_num(dy_12m, 1)}%)")
    if pvp is not None:
        if pvp < 1:
            motivos.append(f"P/VP descontado ({fmt_num(pvp)})")
        elif pvp > 1.8:
            motivos.append(f"P/VP esticado ({fmt_num(pvp)})")
    if roe is not None:
        if roe >= 15:
            motivos.append(f"ROE forte ({fmt_num(roe, 1)}%)")
        elif 0 <= roe < 8:
            motivos.append(f"ROE baixo ({fmt_num(roe, 1)}%)")
    if ifr_14 is not None:
        if 30.0 <= ifr_14 <= 48.0:
            motivos.append(f"IFR em ponto técnico atrativo ({fmt_num(ifr_14, 1)})")
        elif ifr_14 >= 70.0:
            motivos.append(f"IFR sobrecomprado ({fmt_num(ifr_14, 1)})")
        elif ifr_14 < 30.0:
            motivos.append(f"IFR muito sobrevendido ({fmt_num(ifr_14, 1)})")
    if news_resumo != "⚪ Neutro":
        motivos.append(f"notícias 30d: {news_resumo}")
    if pl is not None and pl < 0:
        motivos.append("atenção: lucro negativo")

    return {
        "score_lp": score_lp,
        "score_cp": score_cp,
        "score_geral": score_geral,
        "avg_ms": avg_ms_real,
        "motivos": motivos,
        "veredito": veredito,
        "eh_value_trap": eh_value_trap,
        "preco_teto_modelo": preco_teto_modelo,
        "preco_sobrepreco": preco_sobrepreco,
        "detalhes": {
            "pts_val_lp": round(pts_val_lp, 1),
            "pts_rent_lp": round(pts_rent_lp, 1),
            "pts_saude_lp": round(pts_saude_lp, 1),
            "pts_news_lp": round(pts_news_lp, 1),
            "pts_ifr_cp": round(pts_ifr, 1),
            "pts_medias_cp": round(pts_medias, 1),
            "pts_news_cp": round(pts_news_cp, 1),
            "pts_vol_cp": round(pts_vol, 1),
            "fator_confianca": fator_confianca,
            "n_metodos": n_metodos,
        },
    }


def sort_resultados(lista: list[dict], chave: str, reverso: bool) -> list[dict]:
    validos = [x for x in lista if x.get(chave) is not None]
    nulos = [x for x in lista if x.get(chave) is None]
    validos.sort(key=lambda x: x[chave], reverse=reverso)
    return validos + nulos


def consolidar_carteira_por_ativo(lancamentos: list[dict]) -> dict[str, dict]:
    ordenados = sorted(lancamentos, key=lambda x: x["data"])
    posicoes: dict[str, dict] = {}
    for l in ordenados:
        t = l["ticker"]
        if t not in posicoes:
            posicoes[t] = {"qtd": 0.0, "custo": 0.0, "pm": 0.0, "primeira_data": l["data"], "tipo_ativo": l.get("tipo_ativo", "Ações")}
        p = posicoes[t]
        custos = float(l.get("custos", 0.0) or 0.0)
        if l.get("tipo", "C") == "C":
            p["qtd"] += l["qtd"]
            p["custo"] += (l["qtd"] * l["preco"]) + custos
            p["pm"] = (p["custo"] / p["qtd"]) if p["qtd"] > 0 else 0.0
        else:
            qtd_v = min(p["qtd"], l["qtd"])
            p["qtd"] -= qtd_v
            p["custo"] = p["qtd"] * p["pm"]
    return {t: v for t, v in posicoes.items() if v["qtd"] > 0}


def render_tela_login(key_prefix: str = "login", compacto: bool = False):
    if not gist_configurado():
        st.warning(
            "⚙️ Para ativar contas protegidas por senha e salvamento automático na nuvem sem mudar a URL, "
            "configure `GITHUB_TOKEN` e `GIST_ID` nos **Secrets** do Streamlit."
        )
        return

    if compacto:
        st.caption("🔐 Modo visitante. Faça login para salvar sua Carteira e Favoritos na nuvem:")
    else:
        st.markdown("### 🔐 Acesse sua conta para visualizar e salvar sua Carteira e Favoritos")

    if sso_configurado():
        lbl_sso = "🔵 Entrar com Google" if compacto else "🔵 Entrar com Google (SSO)"
        if st.button(lbl_sso, type="primary", use_container_width=True, key=f"{key_prefix}_sso"):
            auth_cfg = get_secret("auth", {})
            if isinstance(auth_cfg, dict) and "google" in auth_cfg:
                st.login("google")
            else:
                st.login()
        if not compacto:
            st.markdown("---")

    tabs_labels = ["Entrar", "Criar Conta"] if compacto else ["Entrar com E-mail e Senha", "Criar Nova Conta"]
    t_entrar, t_criar = st.tabs(tabs_labels)
    with t_entrar:
        with st.form(f"{key_prefix}_form_in"):
            em = st.text_input("E-mail:", placeholder="seu@email.com", key=f"{key_prefix}_in_em").strip().lower()
            sn = st.text_input("Senha:", type="password", key=f"{key_prefix}_in_sn")
            ok = st.form_submit_button("Entrar", type="primary", use_container_width=True)
            if ok:
                if not em or not sn:
                    st.error("Preencha e-mail e senha.")
                else:
                    try:
                        db, _ = ler_db_gist()
                        u = db["usuarios"].get(em)
                        if not u or not verificar_senha(sn, u.get("salt", ""), u.get("senha_hash", "")):
                            st.error("E-mail ou senha incorretos.")
                        else:
                            st.session_state["usuario_email"] = em
                            st.session_state["metodo_auth"] = "senha"
                            carregar_dados_usuario_nuvem(em)
                            st.rerun()
                    except Exception:
                        st.error("Erro ao verificar login. Confira as credenciais do Gist nos Secrets.")

    with t_criar:
        with st.form(f"{key_prefix}_form_up"):
            em_n = st.text_input("Seu e-mail:", placeholder="seu@email.com", key=f"{key_prefix}_up_em").strip().lower()
            sn_n = st.text_input("Crie uma senha (mín. 6 caracteres):", type="password", key=f"{key_prefix}_up_sn")
            sn_c = st.text_input("Confirme a senha:", type="password", key=f"{key_prefix}_up_sc")
            ok_n = st.form_submit_button("Criar Conta", use_container_width=True)
            if ok_n:
                if "@" not in em_n or "." not in em_n:
                    st.error("Digite um e-mail válido.")
                elif len(sn_n) < 6:
                    st.error("A senha deve ter pelo menos 6 caracteres.")
                elif sn_n != sn_c:
                    st.error("As senhas não coincidem.")
                else:
                    try:
                        db, filename = ler_db_gist()
                        if em_n in db["usuarios"] and db["usuarios"][em_n].get("senha_hash"):
                            st.error("Esse e-mail já possui conta cadastrada.")
                        else:
                            salt_h, hash_h = hash_senha(sn_n)
                            u_atual = db["usuarios"].get(em_n, {})
                            u_atual["salt"] = salt_h
                            u_atual["senha_hash"] = hash_h
                            u_atual.setdefault("favoritos", [])
                            u_atual.setdefault("lancamentos", [])
                            db["usuarios"][em_n] = u_atual
                            salvar_db_gist(db, filename)
                            st.session_state["usuario_email"] = em_n
                            st.session_state["metodo_auth"] = "senha"
                            carregar_dados_usuario_nuvem(em_n)
                            st.success("Conta criada com sucesso!")
                            st.rerun()
                    except Exception:
                        st.error("Erro ao criar conta. Confira as credenciais do Gist nos Secrets.")


@st.dialog("Adicionar Lançamento")
def modal_adicionar_lancamento(tickers_acoes: list[str]):
    op_tipo_op = ["🟢 Compra", "🔴 Venda"]
    if hasattr(st, "segmented_control"):
        op_sel = st.segmented_control("Operação", op_tipo_op, default="🟢 Compra", label_visibility="collapsed", width="stretch")
        if not op_sel:
            op_sel = "🟢 Compra"
    else:
        op_sel = st.radio("Operação", op_tipo_op, horizontal=True, label_visibility="collapsed")
    eh_compra = "Compra" in op_sel

    c1, c2 = st.columns(2)
    with c1:
        tipo_ativo = st.selectbox("Tipo de ativo", ["Ações", "FIIs", "BDRs", "ETFs"], index=0)
    with c2:
        if tipo_ativo == "Ações":
            ativo_sel = st.selectbox("Ativo", ["Selecionar"] + tickers_acoes, index=0)
        else:
            ativo_sel = st.text_input("Ativo (código B3)", placeholder="Ex: MXRF11, IVVB11, AAPL34").strip().upper().replace(".SA", "")

    c3, c4 = st.columns(2)
    with c3:
        dt_l = st.date_input("Data da transação", value=datetime.now(BRT).date(), format="DD/MM/YYYY")
    with c4:
        qtd_l = st.number_input("Quantidade", min_value=1.0, value=1.0, step=1.0)

    c5, c6 = st.columns(2)
    with c5:
        px_l = st.number_input("Preço (R$)", min_value=0.0, value=0.0, step=0.10, format="%.2f")
    with c6:
        custos_l = st.number_input("Outros custos (Opcional) (R$)", min_value=0.0, value=0.0, step=0.50, format="%.2f")

    if eh_compra:
        valor_total = (qtd_l * px_l) + custos_l
    else:
        valor_total = max(0.0, (qtd_l * px_l) - custos_l)

    st.markdown(
        f"<div style='background:rgba(128,128,128,0.16); padding:12px 16px; border-radius:8px; "
        f"display:flex; justify-content:space-between; align-items:center; margin:10px 0 14px 0;'>"
        f"<span style='font-weight:700; font-size:15px;'>Valor total</span>"
        f"<span style='font-weight:700; font-size:17px;'>R$ {fmt_num(valor_total)}</span>"
        f"</div>",
        unsafe_allow_html=True,
    )

    b1, b2 = st.columns([1, 1.4])
    with b1:
        if st.button("Cancelar", use_container_width=True):
            st.rerun()
    with b2:
        if st.button("➕ Adicionar Lançamento", type="primary", use_container_width=True):
            tem_erro = False
            if not ativo_sel or ativo_sel == "Selecionar":
                st.error("⚠️ Ativo: Campo obrigatório")
                tem_erro = True
            if px_l <= 0:
                st.error("⚠️ Preço: Valor inválido (informe um preço maior que R$ 0,00)")
                tem_erro = True
            if not tem_erro:
                nova_lista = list(st.session_state["lancamentos"])
                nova_lista.append({
                    "ticker": ativo_sel,
                    "tipo_ativo": tipo_ativo,
                    "qtd": float(qtd_l),
                    "preco": float(px_l),
                    "custos": float(custos_l),
                    "data": dt_l.strftime("%Y-%m-%d"),
                    "tipo": "C" if eh_compra else "V",
                })
                st.session_state["lancamentos"] = nova_lista
                salvar_dados_usuario_nuvem()
                st.rerun()


# --- ESTADO INICIAL & SESSÃO ---
if "lancamentos" not in st.session_state:
    st.session_state["lancamentos"] = []
if "favoritos" not in st.session_state:
    st.session_state["favoritos"] = []
if "comp_selecionados" not in st.session_state:
    st.session_state["comp_selecionados"] = []
if "raiox_visivel" not in st.session_state:
    st.session_state["raiox_visivel"] = False

try:
    if getattr(st.user, "is_logged_in", False) and getattr(st.user, "email", None):
        em_sso = st.user.email.lower()
        st.session_state["usuario_email"] = em_sso
        st.session_state["metodo_auth"] = "sso"
        if st.session_state.get("nuvem_carregada_para") != em_sso:
            carregar_dados_usuario_nuvem(em_sso)
except Exception:
    pass

usuario_atual = st.session_state.get("usuario_email")


# --- INTERFACE PRINCIPAL ---
st.title("📊 Painel Completo da B3 — Valuation, Raio-X & Carteira")
st.caption("Busca ao vivo, Setor BESST, Favoritos por usuário, gráfico interativo, balanço anual CVM, notícias e carteira protegida por login.")

try:
    with st.spinner("Carregando todos os ativos da B3..."):
        todos_ativos = carregar_todos_ativos_b3()
        setores_dict = carregar_setores_fundamentus()
except Exception as exc:
    st.error(f"Erro ao conectar com o Fundamentus: {exc}")
    st.stop()

tickers_b3 = sorted([a["ticker"] for a in todos_ativos])

# --- BARRA LATERAL ---
with st.sidebar:
    st.header("👤 Sua Conta")
    if usuario_atual:
        st.success(f"Logado: **{usuario_atual}**")
        if st.button("🚪 Sair da Conta", use_container_width=True):
            metodo = st.session_state.get("metodo_auth")
            for k in ("usuario_email", "metodo_auth", "nuvem_carregada_para"):
                st.session_state.pop(k, None)
            st.session_state["favoritos"] = []
            st.session_state["ms_favs"] = []
            st.session_state["lancamentos"] = []
            if metodo == "sso":
                st.logout()
            st.rerun()
    else:
        render_tela_login(key_prefix="sidebar_login", compacto=True)

    st.divider()
    st.header("🔍 Filtros da Bolsa")
    st.caption("Combine quantos filtros desejar ao mesmo tempo.")

    opcoes_listas = [
        "🌟 BESST (Bancos, Energia, Saneamento, Seguros e Telecom)",
        "⭐ Apenas Meus Favoritos",
        "💼 Apenas Minha Carteira",
    ]
    opcoes_setores_exibir = sorted(
        [SETOR_ALIAS.get(s, s) for s in setores_dict.keys()],
        key=_norm_txt,
    )

    setor_url = st.query_params.get("setor", "")
    default_listas = [setor_url] if setor_url in opcoes_listas else []
    default_setores = [SETOR_ALIAS.get(setor_url, setor_url)] if SETOR_ALIAS.get(setor_url, setor_url) in opcoes_setores_exibir else []

    filtro_listas = st.multiselect(
        "Listas rápidas:",
        options=opcoes_listas,
        default=default_listas,
        placeholder="Todas (ou escolha 1 ou mais)",
        help="Favoritos e Carteira filtram seus ativos (interseção entre si). BESST soma-se aos Setores específicos abaixo.",
    )
    filtro_setores = st.multiselect(
        "Setores específicos:",
        options=opcoes_setores_exibir,
        default=default_setores,
        placeholder="Todos os setores",
        help="Soma-se ao BESST (se selecionado) e filtra em conjunto com Favoritos/Carteira.",
    )

    liq_min_opcoes = {
        "R$ 0 (mostrar literalmente todas)": 0,
        "R$ 100 mil/dia (recomendado)": 100_000,
        "R$ 1 milhão/dia (alta liquidez)": 1_000_000,
    }
    liq_keys = list(liq_min_opcoes.keys())
    liq_url = st.query_params.get("liq", liq_keys[0])
    idx_liq = liq_keys.index(liq_url) if liq_url in liq_keys else 0
    liq_label = st.selectbox("Liquidez mínima (2 meses):", liq_keys, index=idx_liq)
    liq_min = liq_min_opcoes[liq_label]

    busca_tickers = st.text_input(
        "Filtrar códigos na barra (opcional):",
        value=st.query_params.get("busca", ""),
        placeholder="Ex: BBAS3, BBDC3, TAEE11",
    )

    st.divider()
    st.subheader("⭐ Ações Favoritas")
    if not tickers_b3:
        st.caption("⚠️ Lista de ativos indisponível no momento; seus favoritos salvos foram preservados.")
    else:
        def _ao_colar_favs_bridge(tickers_validos: list[str]):
            raw_fp = st.session_state.get("favs_paste_bridge", "").strip()
            st.session_state["favs_paste_bridge"] = ""
            if not raw_fp:
                return
            texto_siglas = raw_fp.rsplit("|", 1)[0] if "|" in raw_fp else raw_fp
            set_b3 = set(tickers_validos)
            encontrados: list[str] = []
            ignorados: list[str] = []
            vistos_f: set[str] = set()
            for raw_tok in re.split(r"[\s,;|\t\r\n/\\]+", texto_siglas.upper()):
                tok = re.sub(r"^[^A-Z0-9.]+|[^A-Z0-9.]+$", "", raw_tok.strip())
                tok = re.sub(r"\.SA$", "", tok)
                tok = re.sub(r"^[^A-Z0-9]+|[^A-Z0-9]+$", "", tok)
                if not tok or tok in vistos_f:
                    continue
                vistos_f.add(tok)
                if tok in set_b3:
                    encontrados.append(tok)
                else:
                    ignorados.append(tok)

            if not encontrados:
                st.session_state["_favs_paste_msg"] = (
                    "warning",
                    "Nenhuma sigla válida da B3 encontrada no texto colado.",
                )
                return

            nova_lista = list(dict.fromkeys(list(st.session_state.get("favoritos", [])) + encontrados))
            st.session_state["favoritos"] = nova_lista
            st.session_state["ms_favs"] = list(nova_lista)
            aviso_ig = f" | Não encontradas: {', '.join(ignorados)}" if ignorados else ""
            st.session_state["_favs_paste_msg"] = (
                "success",
                f"{len(encontrados)} sigla(s) adicionada(s): {', '.join(encontrados)}{aviso_ig}",
            )
            salvar_dados_usuario_nuvem()

        opcoes_favs = sorted(set(tickers_b3) | set(st.session_state["favoritos"]))
        if "ms_favs" not in st.session_state:
            st.session_state["ms_favs"] = list(st.session_state["favoritos"])
        favs_sel = st.multiselect(
            "Selecione suas favoritas:",
            options=opcoes_favs,
            key="ms_favs",
            help="Você pode digitar ou colar várias siglas de uma vez (uma por linha, vírgula ou espaço) direto aqui.",
        )
        if favs_sel != st.session_state["favoritos"]:
            st.session_state["favoritos"] = favs_sel
            salvar_dados_usuario_nuvem()
            st.rerun()

        st.text_input(
            "favs_paste_bridge_input",
            key="favs_paste_bridge",
            label_visibility="collapsed",
            on_change=_ao_colar_favs_bridge,
            args=(tickers_b3,),
        )

        st.markdown(
            "<style>"
            "div[data-testid='stElementContainer']:has(input[aria-label='favs_paste_bridge_input']),"
            "div.element-container:has(input[aria-label='favs_paste_bridge_input']),"
            "div[data-testid='stElementContainer']:has(iframe[height='0']),"
            "div.element-container:has(iframe[height='0']){"
            "position:fixed!important;left:-9999px!important;top:50%!important;"
            "width:1px!important;height:1px!important;opacity:0!important;"
            "overflow:hidden!important;margin:0!important;padding:0!important;}"
            "</style>",
            unsafe_allow_html=True,
        )

        _usa_st_html_fav = hasattr(st, "html") and "unsafe_allow_javascript" in inspect.signature(st.html).parameters
        _js_favs_paste = """
        <script>
        (function() {
            const pWin = __USE_PARENT__ ? window.parent : window;
            const pDoc = pWin.document;

            if (pWin.__favsPasteHandlerAttached) return;
            pWin.__favsPasteHandlerAttached = true;

            pDoc.addEventListener("paste", function(e) {
                const ms = e.target && e.target.closest ? e.target.closest('div[data-testid="stMultiSelect"]') : null;
                if (!ms) return;
                const lbl = ms.querySelector('[data-testid="stWidgetLabel"], label');
                const lblTxt = lbl ? (lbl.innerText || lbl.textContent || "") : "";
                if (lblTxt.indexOf("Selecione suas favoritas") === -1) return;

                const cd = e.clipboardData || pWin.clipboardData;
                const pasted = cd ? (cd.getData("text") || "") : "";
                if (!pasted) return;

                const tokens = pasted.toUpperCase().replace(/\\.SA\\b/g, "").split(/[\\s,;|\\t\\r\\n/\\\\]+/).filter(Boolean);
                const multiOuSep = tokens.length >= 2 || (tokens.length === 1 && /[,;\\r\\n]|\\.SA\\b/i.test(pasted));
                if (!multiOuSep) return;

                e.preventDefault();
                e.stopPropagation();

                if (e.target && e.target.blur) {
                    try { e.target.blur(); } catch (err) {}
                }

                const inp = pDoc.querySelector('input[aria-label="favs_paste_bridge_input"]');
                if (!inp) return;
                const payload = pasted.replace(/[\\r\\n\\t]+/g, " ").trim() + "|" + Date.now();
                const setter = Object.getOwnPropertyDescriptor(pWin.HTMLInputElement.prototype, "value").set;
                try { inp.focus({ preventScroll: true }); } catch (err) {}
                setter.call(inp, payload);
                inp.dispatchEvent(new Event("input", { bubbles: true }));
                inp.dispatchEvent(new Event("change", { bubbles: true }));
                setTimeout(function() {
                    const evInit = { key: "Enter", code: "Enter", keyCode: 13, which: 13, bubbles: true, cancelable: true };
                    inp.dispatchEvent(new KeyboardEvent("keydown", evInit));
                    inp.dispatchEvent(new KeyboardEvent("keypress", evInit));
                    inp.dispatchEvent(new KeyboardEvent("keyup", evInit));
                    inp.dispatchEvent(new FocusEvent("blur", { bubbles: true }));
                }, 50);
            }, true);
        })();
        </script>
        """.replace("__USE_PARENT__", "false" if _usa_st_html_fav else "true")

        if _usa_st_html_fav:
            st.html(_js_favs_paste, unsafe_allow_javascript=True)
        else:
            components.html(_js_favs_paste, height=0)

        msg_favs = st.session_state.pop("_favs_paste_msg", None)
        if msg_favs:
            tp_msg, txt_msg = msg_favs
            if tp_msg == "success":
                st.success(txt_msg)
            else:
                st.warning(txt_msg)

    if st.button("🔄 Atualizar Dados", type="primary", use_container_width=True):
        st.cache_data.clear()
        st.rerun()

st.query_params["liq"] = liq_label
if busca_tickers.strip():
    st.query_params["busca"] = busca_tickers.strip()
elif "busca" in st.query_params:
    del st.query_params["busca"]

posicoes_carteira = consolidar_carteira_por_ativo(st.session_state["lancamentos"]) if usuario_atual else {}

mapa_setores_ativos: dict[str, str] = {}

ativos_filtrados = todos_ativos

if "⭐ Apenas Meus Favoritos" in filtro_listas:
    fav_set = set(st.session_state["favoritos"])
    ativos_filtrados = [a for a in ativos_filtrados if a["ticker"] in fav_set]
if "💼 Apenas Minha Carteira" in filtro_listas:
    ativos_filtrados = [a for a in ativos_filtrados if a["ticker"] in posicoes_carteira]

if busca_tickers.strip():
    lista_busca = {x.strip().upper().replace(".SA", "") for x in busca_tickers.split(",") if x.strip()}
    ativos_filtrados = [a for a in ativos_filtrados if a["ticker"] in lista_busca]

if liq_min > 0:
    ativos_filtrados = [a for a in ativos_filtrados if a["liq_2m"] >= liq_min]

setores_alvo: set[str] = set()
if "🌟 BESST (Bancos, Energia, Saneamento, Seguros e Telecom)" in filtro_listas:
    setores_alvo |= BESST_SETORES
if filtro_setores:
    setores_alvo |= {ALIAS_PARA_SETOR.get(s, s) for s in filtro_setores}

if setores_alvo:
    ids_alvo = tuple(sorted({setores_dict[s] for s in setores_alvo if s in setores_dict}))
    if ids_alvo:
        with st.spinner("Carregando setores selecionados..."):
            mapa_setores_ativos.update(carregar_tickers_por_setor(ids_alvo))

    if 0 < len(ativos_filtrados) <= 35:
        falt_setor = [a["ticker"] for a in ativos_filtrados if not mapa_setores_ativos.get(a["ticker"])]
        if falt_setor:
            def _fetch_setor_det(tk_s: str):
                det_s = buscar_detalhes_fundamentus(tk_s)
                return tk_s, " ".join((det_s.get("Setor") or "").split())

            with ThreadPoolExecutor(max_workers=4) as ex_s:
                for tk_s, st_nome in ex_s.map(_fetch_setor_det, falt_setor):
                    if st_nome:
                        mapa_setores_ativos[tk_s] = st_nome

    ativos_filtrados = [a for a in ativos_filtrados if mapa_setores_ativos.get(a["ticker"]) in setores_alvo]

ids_fin_seg = tuple(sorted({setores_dict[s] for s in ("Intermediários Financeiros", "Previdência e Seguros") if s in setores_dict}))
mapa_fin_seg = carregar_tickers_por_setor(ids_fin_seg) if ids_fin_seg else {}

preliminares = []
for a in ativos_filtrados:
    a_pre = {**a, "eh_banco_seg": a["ticker"] in mapa_fin_seg}
    pt_bazin = a["dpa_12m"] / 0.06 if a["dpa_12m"] > 0 else None
    graham = math.sqrt(22.5 * a["lpa"] * a["vpa"]) if (a["lpa"] and a["vpa"] and a["lpa"] > 0 and a["vpa"] > 0) else None
    res_pre = calcular_score(a_pre, None, None, pt_bazin, graham)
    preliminares.append((res_pre["score_geral"], a))
preliminares.sort(key=lambda x: x[0], reverse=True)

carregar_todos_yf = False
if len(ativos_filtrados) > 55:
    carregar_todos_yf = st.checkbox(
        f"📥 Carregar histórico de 6 anos e Projetivo (Yahoo Finance) para TODOS os {len(ativos_filtrados)} ativos (padrão: Top 30 mais atrativos)",
        value=False,
    )

limite_yf = len(preliminares) if (len(preliminares) <= 55 or carregar_todos_yf) else 30
tickers_para_yf = [item[1]["ticker"] for item in preliminares[:limite_yf]]
ativo_url = st.query_params.get("ativo", "").strip().upper()
extras_obrigatorios = list(posicoes_carteira.keys()) + st.session_state["favoritos"] + ([ativo_url] if ativo_url else [])
for ex in extras_obrigatorios:
    if ex and ex not in tickers_para_yf:
        tickers_para_yf.append(ex)

with st.spinner(f"Buscando dados de 6 anos, indicadores técnicos e notícias para {len(tickers_para_yf)} ativos..."):
    dados_yf = buscar_yahoo_lote(tuple(tickers_para_yf))
    dados_news = buscar_sentimento_noticias_lote(tuple(tickers_para_yf))


def montar_item_completo(a: dict) -> dict:
    t = a["ticker"]
    yf_info = dados_yf.get(t, {})
    news_info = dados_news.get(t, {})
    cot = yf_info.get("cotacao_yf") or a.get("cotacao") or 0.0
    nome = yf_info.get("nome") or mapa_setores_ativos.get(t) or t
    lpa = a.get("lpa") if a.get("lpa") is not None else yf_info.get("lpa_yf")
    vpa = a.get("vpa") if a.get("vpa") is not None else yf_info.get("vpa_yf")
    roe = a.get("roe") if a.get("roe") is not None else yf_info.get("roe_yf")
    pl = (cot / lpa) if (cot > 0 and lpa is not None and lpa != 0) else a.get("pl")
    pvp = (cot / vpa) if (cot > 0 and vpa is not None and vpa != 0) else a.get("pvp")

    dpa_12m = yf_info.get("dpa_12m_yf") if yf_info.get("dpa_12m_yf") is not None else (a.get("dpa_12m") or 0.0)
    dy_12m = (dpa_12m / cot) * 100 if (dpa_12m and cot > 0) else (a.get("dy_12m") or 0.0)
    dpa_med_6a = yf_info.get("dpa_med_6a")
    anos_hist = yf_info.get("anos_hist", 0)
    dpa_proj = yf_info.get("dpa_proj")

    pt_med = (dpa_med_6a / 0.06) if (dpa_med_6a and dpa_med_6a > 0) else None
    pt_proj = (dpa_proj / 0.06) if (dpa_proj and dpa_proj > 0) else None
    pt_bazin = (dpa_12m / 0.06) if (dpa_12m and dpa_12m > 0) else None
    graham = math.sqrt(22.5 * lpa * vpa) if (lpa and vpa and lpa > 0 and vpa > 0) else None

    setor_oficial_t = mapa_setores_ativos.get(t, "") or mapa_fin_seg.get(t, "")
    setor_exib_t = SETOR_CURTO.get(setor_oficial_t, setor_oficial_t)
    eh_banco_seg = (t in mapa_fin_seg) or any(
        k in _norm_txt(setor_oficial_t) for k in ("banco", "intermediarios financeiros", "seguro", "previdencia")
    )

    item = {
        **a,
        "cotacao": cot, "nome": nome, "setor_nome": setor_exib_t, "eh_banco_seg": eh_banco_seg,
        "pl": pl, "pvp": pvp, "lpa": lpa, "vpa": vpa, "roe": roe,
        "dpa_12m": dpa_12m, "dy_12m": dy_12m,
        "dpa_med_6a": dpa_med_6a, "anos_hist": anos_hist, "dpa_proj": dpa_proj,
        "pt_med": pt_med, "pt_proj": pt_proj, "pt_bazin": pt_bazin, "graham": graham,
        "ifr_14": yf_info.get("ifr_14"),
        "mm20": yf_info.get("mm20"),
        "mm50": yf_info.get("mm50"),
        "mm200": yf_info.get("mm200"),
        "dist_mm50_pct": yf_info.get("dist_mm50_pct"),
        "dist_mm200_pct": yf_info.get("dist_mm200_pct"),
        "dist_max_52s_pct": yf_info.get("dist_max_52s_pct"),
        "razao_volume": yf_info.get("razao_volume"),
        "news_score": news_info.get("news_score", 0.0),
        "news_resumo": news_info.get("news_resumo", "⚪ Neutro"),
        "news_qtd_30d": news_info.get("qtd_30d", 0),
        "news_qtd_7d": news_info.get("qtd_7d", 0),
    }
    res_score = calcular_score(item, pt_med, pt_proj, pt_bazin, graham)
    item["score_lp"] = res_score["score_lp"]
    item["score_cp"] = res_score["score_cp"]
    item["score_geral"] = res_score["score_geral"]
    item["score"] = res_score["score_geral"]
    item["avg_ms"] = res_score["avg_ms"]
    item["motivos"] = res_score["motivos"]
    item["veredito"] = res_score["veredito"]
    item["eh_value_trap"] = res_score["eh_value_trap"]
    item["preco_teto_modelo"] = res_score["preco_teto_modelo"]
    item["preco_sobrepreco"] = res_score["preco_sobrepreco"]
    item["detalhes_score"] = res_score["detalhes"]
    return item


resultados = [montar_item_completo(a) for _, a in preliminares]
resultados.sort(key=lambda x: x["score_geral"], reverse=True)
for idx, r in enumerate(resultados, start=1):
    r["pos_ranking"] = idx

tab1, tab2, tab3 = st.tabs([
    f"📊 Tabela & Raio-X ({len(resultados)} ativos)",
    "⚖️ Comparar Ativos",
    f"🔒 Minha Carteira ({len(posicoes_carteira) if usuario_atual else 'Login'})",
])

# ==================== ABA 1: TABELA, RAIO-X, RANKING E NOTÍCIAS ====================
with tab1:
    if not resultados:
        st.info("Nenhum ativo encontrado no filtro atual.")
    else:
        MODO_SCORE_OPCOES = {
            "🏆 Geral (Melhor Compra Equilibrada)": "score_geral",
            "🏛️ Longo Prazo (Fundamentos & Dividendos)": "score_lp",
            "⚡ Curto Prazo (Timing & Catalisadores)": "score_cp",
        }
        VEREDITOS_OPCOES = [
            "🟢 Excelente (Forte Atratividade)",
            "🔵 Bom (Acúmulo LP)",
            "🟣 Esticado (Alerta Topo/Sobrepreço)",
            "🟠 Indeciso (Sinais Mistos)",
            "🟡 Regular (Neutro)",
            "🔴 Crítico (Risco Alto)",
        ]

        c_modo_sc, c_filt_ver = st.columns([2.2, 1.5])
        with c_modo_sc:
            modo_score_lbl = st.radio(
                "🎯 Modo de Análise / Score:",
                options=list(MODO_SCORE_OPCOES.keys()),
                index=0,
                horizontal=True,
                key="tab1_modo_score",
            )
        with c_filt_ver:
            filtro_vereditos = st.multiselect(
                "🏷️ Filtrar por Veredito do Modelo:",
                options=VEREDITOS_OPCOES,
                default=[],
                placeholder="Todos os vereditos (ex: 🟢 Excelente, 🔵 Bom)",
                key="tab1_filtro_veredito",
            )

        chave_score_ativo = MODO_SCORE_OPCOES[modo_score_lbl]
        resultados_tab = [
            {**r, "pos_ranking": idx_m, "score_ativo": r[chave_score_ativo]}
            for idx_m, r in enumerate(
                sorted(resultados, key=lambda x: x[chave_score_ativo], reverse=True),
                start=1,
            )
        ]
        if filtro_vereditos:
            ver_set = set(filtro_vereditos)
            resultados_tab = [r for r in resultados_tab if r.get("veredito") in ver_set]

        with st.expander(f"📋 Tabela Comparativa ({len(resultados_tab)} ativos no filtro) — clique para minimizar/maximizar | clique em qualquer linha para abrir/fechar o Raio-X", expanded=True):
            c_busca, c_ord1, c_ord2, c_ord3 = st.columns([1.8, 1.8, 1.4, 1.2])
            opcoes_ordenacao = {
                "Atratividade (Score Ativo)": "score_ativo",
                "Score Geral (60% LP + 40% CP)": "score_geral",
                "Score Longo Prazo (LP)": "score_lp",
                "Score Curto Prazo (CP)": "score_cp",
                "Margem de Segurança Média (%)": "avg_ms",
                "IFR (14 dias)": "ifr_14",
                "Notícias 30d (News Score)": "news_score",
                "Cotação (R$)": "cotacao",
                "Dividend Yield 12m (%)": "dy_12m",
                "P/L": "pl",
                "P/VP": "pvp",
                "ROE (%)": "roe",
                "ROIC (%)": "roic",
                "Preço Teto Médio (6a)": "pt_med",
                "Preço Teto Projetivo": "pt_proj",
                "Preço-Teto Bazin (12m)": "pt_bazin",
                "Preço Justo Graham": "graham",
                "Ticker (A-Z)": "ticker",
            }
            with c_busca:
                busca_tabela = st_keyup("🔎 Buscar na tabela (ao digitar):", placeholder="Ex: PETR, BBAS, CEMIG", debounce=200, key="busca_live")
            with c_ord1:
                col_escolhida = st.selectbox("Ordenar por coluna:", list(opcoes_ordenacao.keys()), index=0)
            with c_ord2:
                dir_padrao = 1 if col_escolhida in ("P/L", "P/VP", "Ticker (A-Z)") else 0
                direcao = st.selectbox("Ordem:", ["Decrescente (Maior → Menor)", "Crescente (Menor → Maior)"], index=dir_padrao)
            with c_ord3:
                max_linhas = st.number_input("Exibir (0 = todos):", min_value=0, max_value=1000, value=50, step=10)

            lista_tab = resultados_tab
            if busca_tabela and busca_tabela.strip():
                termo = busca_tabela.strip().upper()
                lista_tab = [r for r in resultados_tab if termo in r["ticker"] or termo in r["nome"].upper()]

            chave_ord = opcoes_ordenacao[col_escolhida]
            reverso = direcao.startswith("Decrescente")
            resultados_ordenados = sort_resultados(lista_tab, chave_ord, reverso)
            exibir = resultados_ordenados if max_linhas == 0 else resultados_ordenados[:int(max_linhas)]

            st.caption(f"Mostrando **{len(exibir)}** de **{len(lista_tab)}** ativos.")

            if not exibir:
                st.warning("Nenhum ativo corresponde à busca digitada na tabela.")
            else:
                def _ao_clicar_comparar_tabela():
                    raw_c = st.session_state.get("comp_bridge", "").strip().upper()
                    st.session_state["comp_bridge"] = ""
                    if not raw_c:
                        return
                    tk_c = raw_c.split("|")[0].strip()
                    if not tk_c:
                        return
                    sel_c = list(st.session_state.get("comp_selecionados", []))
                    if tk_c in sel_c:
                        sel_c.remove(tk_c)
                    else:
                        sel_c.append(tk_c)
                    st.session_state["comp_selecionados"] = sel_c
                    st.session_state["ms_comp"] = sel_c

                st.text_input(
                    "comp_bridge_input",
                    key="comp_bridge",
                    label_visibility="collapsed",
                    on_change=_ao_clicar_comparar_tabela,
                )

                comp_set = set(st.session_state.get("comp_selecionados", []))
                if comp_set:
                    c_info_cmp, c_btn_cmp = st.columns([4, 1])
                    with c_info_cmp:
                        st.info(
                            f"⚖️ **{len(comp_set)} ativo(s) selecionado(s) para comparar:** "
                            f"{', '.join(st.session_state['comp_selecionados'])} — "
                            "acesse a aba **⚖️ Comparar Ativos** para visualizar (e adicionar mais se quiser)."
                        )
                    with c_btn_cmp:
                        if st.button("🧹 Limpar seleção", key="btn_limpar_comp", use_container_width=True):
                            st.session_state["comp_selecionados"] = []
                            st.session_state["ms_comp"] = []
                            st.rerun()

                st.markdown(
                    "<style>"
                    "div[data-testid='stElementContainer']:has(input[aria-label='raiox_bridge_input']),"
                    "div.element-container:has(input[aria-label='raiox_bridge_input']),"
                    "div[data-testid='stElementContainer']:has(input[aria-label='comp_bridge_input']),"
                    "div.element-container:has(input[aria-label='comp_bridge_input']),"
                    "div[data-testid='stElementContainer']:has(iframe[height='0']),"
                    "div.element-container:has(iframe[height='0']){"
                    "position:fixed!important;left:-9999px!important;top:50%!important;"
                    "width:1px!important;height:1px!important;opacity:0!important;"
                    "overflow:hidden!important;margin:0!important;padding:0!important;}"
                    "div[data-testid='stVerticalBlock']:has(> div .raiox-table-host),"
                    "div[data-testid='stVerticalBlock']:has(> div > div .raiox-table-host){gap:0!important;}"
                    ".val-table-wrap{width:100%;overflow-x:auto;margin:0;padding:0;}"
                    ".val-table{width:100%;border-collapse:collapse;font-size:13px;line-height:1.4;margin:0;}"
                    ".val-table th{position:relative;user-select:none;background-color:rgba(128,128,128,0.18);text-align:left;padding:8px 8px;border-bottom:2px solid rgba(128,128,128,0.35);border-right:1px solid rgba(128,128,128,0.22);font-weight:600;font-size:12px;overflow:hidden;text-overflow:ellipsis;}"
                    ".val-table td{padding:8px 8px;border-bottom:1px solid rgba(128,128,128,0.22);border-right:1px solid rgba(128,128,128,0.12);vertical-align:middle;overflow-wrap:break-word;}"
                    ".val-table tbody tr.raiox-row{cursor:pointer;}"
                    ".val-table tr:hover td{background-color:rgba(128,128,128,0.08);}"
                    ".val-table tr.raiox-active-row td{background-color:rgba(59,130,246,0.14)!important;border-bottom-color:rgba(59,130,246,0.45)!important;}"
                    ".col-resizer{position:absolute;top:0;right:-3px;width:7px;height:100%;cursor:col-resize;z-index:10;}"
                    ".col-resizer:hover,.col-resizer.resizing{background:rgba(96,165,250,0.55);}"
                    ".comp-chk-btn{position:relative;display:inline-flex;align-items:center;justify-content:center;width:18px;height:18px;min-width:18px;min-height:18px;border-radius:4px!important;border:1.5px solid rgba(148,163,184,0.75);background:transparent;cursor:pointer;user-select:none;outline:none!important;transition:background-color 0.12s ease,border-color 0.12s ease;}"
                    ".comp-chk-btn:hover{border-color:#60a5fa;}"
                    ".comp-chk-btn.checked{background:#3b82f6!important;border-color:#3b82f6!important;}"
                    ".comp-chk-btn.checked::after{content:'';display:block;width:5px;height:9px;border:solid #ffffff;border-width:0 2.2px 2.2px 0;transform:rotate(45deg);margin-bottom:2px;}"
                    "</style>",
                    unsafe_allow_html=True,
                )

                def _ao_clicar_ticker_tabela():
                    raw_rx = st.session_state.get("raiox_bridge", "").strip().upper()
                    st.session_state["raiox_bridge"] = ""
                    if not raw_rx:
                        return
                    tk_clicado = raw_rx.split("|")[0].strip()
                    if not tk_clicado:
                        return
                    if st.session_state.get("raiox_visivel", False) and st.session_state.get("raiox_ativo_sel") == tk_clicado:
                        st.session_state["raiox_visivel"] = False
                    else:
                        st.session_state["raiox_ativo_sel"] = tk_clicado
                        st.session_state["raiox_visivel"] = True

                @st.fragment
                def render_tabela_e_raiox(exibir_rows: list[dict], opcoes_rx: list[str], mapa_res: dict[str, dict], comp_ativos: set[str], modo_score_chave: str = "score_geral"):
                    st.text_input(
                        "raiox_bridge_input",
                        key="raiox_bridge",
                        label_visibility="collapsed",
                        on_change=_ao_clicar_ticker_tabela,
                    )
                    if "raiox_ativo_sel" not in st.session_state:
                        st.session_state["raiox_ativo_sel"] = ativo_url if ativo_url in opcoes_rx else opcoes_rx[0]
                        if ativo_url and ativo_url in opcoes_rx:
                            st.session_state["raiox_visivel"] = True
                    elif st.session_state["raiox_ativo_sel"] not in opcoes_rx:
                        st.session_state["raiox_ativo_sel"] = opcoes_rx[0]

                    visivel = st.session_state.get("raiox_visivel", False)
                    ativo_escolhido = st.session_state.get("raiox_ativo_sel", opcoes_rx[0])

                    fav_set = set(st.session_state["favoritos"])
                    linhas_html = []
                    idx_split = None
                    for i_row, r in enumerate(exibir_rows):
                        cot = r["cotacao"]
                        sufixo_6a = "*" if 0 < r["anos_hist"] < 6 else ""

                        pl_txt = fmt_num(r["pl"]) if r["pl"] is not None else "N/A"
                        if r["pvp"] is not None:
                            cor_pvp = "#22c55e" if r["pvp"] < 1 else "#ef4444"
                            emoji_pvp = "🟢" if r["pvp"] < 1 else "🔴"
                            pvp_html = f"<span style='color:{cor_pvp}; font-weight:600;'>{fmt_num(r['pvp'])} {emoji_pvp}</span>"
                        else:
                            pvp_html = "N/A"
                        roe_txt = f"{fmt_num(r['roe'], 1)}%" if r["roe"] is not None else "N/A"

                        lpa_txt = f"R$ {fmt_num(r['lpa'])}" if r["lpa"] is not None else "N/A"
                        vpa_txt = f"R$ {fmt_num(r['vpa'])}" if r["vpa"] is not None else "N/A"
                        dpa6_txt = f"R$ {fmt_num(r['dpa_med_6a'])}" if r["dpa_med_6a"] is not None else "—"
                        dpap_txt = f"R$ {fmt_num(r['dpa_proj'])}" if r["dpa_proj"] is not None else "—"

                        nome_esc = html.escape(r["nome"])
                        setor_badge = f"<br><small style='opacity:0.72;'>{html.escape(r['setor_nome'])}</small>" if r["setor_nome"] else ""
                        estrela = " ⭐" if r["ticker"] in fav_set else ""
                        chk_cls = "comp-chk-btn checked" if r["ticker"] in comp_ativos else "comp-chk-btn"
                        eh_linha_rx = visivel and r["ticker"] == ativo_escolhido
                        tr_cls = " class='raiox-row raiox-active-row'" if eh_linha_rx else " class='raiox-row'"
                        if eh_linha_rx:
                            idx_split = i_row

                        score_at = r.get("score_ativo", r.get(modo_score_chave, r.get("score_geral", r["score"])))
                        veredito_r = r.get("veredito", "🟡 Regular (Neutro)")
                        badge_v = badge_veredito_html(veredito_r)
                        ifr_val = r.get("ifr_14")
                        if ifr_val is None:
                            ifr_ic = "📊 —"
                        elif 30.0 <= ifr_val <= 48.0:
                            ifr_ic = f"🎯 {fmt_num(ifr_val, 0)}"
                        elif ifr_val < 30.0:
                            ifr_ic = f"🧊 {fmt_num(ifr_val, 0)}"
                        elif ifr_val >= 70.0:
                            ifr_ic = f"🔥 {fmt_num(ifr_val, 0)}"
                        else:
                            ifr_ic = f"📊 {fmt_num(ifr_val, 0)}"
                        news_res_r = r.get("news_resumo", "⚪ Neutro")
                        news_sc_r = float(r.get("news_score") or 0.0)
                        if "🚨" in news_res_r:
                            news_ic = f"🚨 {news_sc_r:+.0f}"
                        elif "🔴" in news_res_r:
                            news_ic = f"📰🔴 {news_sc_r:+.0f}"
                        elif "🟢" in news_res_r:
                            news_ic = f"📰🟢 {news_sc_r:+.0f}"
                        else:
                            news_ic = "📰⚪ 0"

                        linha = (
                            f"<tr{tr_cls} data-raiox-ticker='{r['ticker']}'>"
                            f"<td style='text-align:center;'><span class='{chk_cls}' data-comp-ticker='{r['ticker']}' role='checkbox' aria-checked='{'true' if r['ticker'] in comp_ativos else 'false'}' title='Selecionar para Comparar Ativos'></span></td>"
                            f"<td style='text-align:center; line-height:1.35;'>"
                            f"<span style='font-weight:700;'>{r['pos_ranking']}º</span> · <strong>{fmt_num(score_at, 1)}</strong>"
                            f"<br>{badge_v}"
                            f"<br><small style='opacity:0.85; white-space:nowrap;' title='IFR 14d: {ifr_ic} | Notícias 30d: {html.escape(news_res_r)}'>{ifr_ic} | {news_ic}</small>"
                            f"</td>"
                            f"<td><span style='color:#60a5fa; font-weight:700;'>{r['ticker']}</span>{estrela}<br><small style='opacity:0.88;'>{nome_esc}</small>{setor_badge}</td>"
                            f"<td><strong>R$ {fmt_num(cot)}</strong><br><small>DY: {fmt_num(r['dy_12m'])}%</small></td>"
                            f"<td>P/L: {pl_txt}<br>P/VP: {pvp_html}<br>ROE: {roe_txt}</td>"
                            f"<td>LPA: {lpa_txt} | VPA: {vpa_txt}<br>12m: R$ {fmt_num(r['dpa_12m'])} | 6a: {dpa6_txt}<br>Proj: {dpap_txt}</td>"
                            f"<td>{html_preco_ms(r['pt_med'], cot, sufixo_6a)}</td>"
                            f"<td>{html_preco_ms(r['pt_proj'], cot)}</td>"
                            f"<td>{html_preco_ms(r['pt_bazin'], cot)}</td>"
                            f"<td>{html_preco_ms(r['graham'], cot)}</td>"
                            "</tr>"
                        )
                        linhas_html.append(linha)

                    thead_html = (
                        "<thead><tr>"
                        "<th style='text-align:center;'>⚖️</th>"
                        "<th style='text-align:center;'>Rank / Score<br><small>Veredito | IFR | News</small></th>"
                        "<th>Ticker / Empresa</th>"
                        f"<th>Cotação ({datetime.now(BRT).strftime('%d/%m/%Y %H:%M')}) & DY</th>"
                        "<th>Indicadores<br><small>(P/L | P/VP | ROE)</small></th>"
                        "<th>Dados Base<br><small>(LPA | VPA | DPAs)</small></th>"
                        "<th>Preço Teto Médio (6a) & MS</th>"
                        "<th>Preço Teto Projetivo & MS</th>"
                        "<th>Preço-Teto Bazin (12m) & MS</th>"
                        "<th>Preço Justo Graham & MS</th>"
                        "</tr></thead>"
                    )

                    with st.container():
                        st.markdown("<span class='raiox-table-host' style='display:none;'></span>", unsafe_allow_html=True)
                        if idx_split is None:
                            st.markdown(
                                f"<div class='val-table-wrap val-table-wrap-top'><table class='val-table val-table-top'>{thead_html}<tbody>{''.join(linhas_html)}</tbody></table></div>",
                                unsafe_allow_html=True,
                            )
                        else:
                            st.markdown(
                                f"<div class='val-table-wrap val-table-wrap-top'><table class='val-table val-table-top'>{thead_html}<tbody>{''.join(linhas_html[:idx_split + 1])}</tbody></table></div>",
                                unsafe_allow_html=True,
                            )
                            with st.container(border=True):
                                c_rx1, c_rx2 = st.columns([3.8, 1])
                                with c_rx1:
                                    st.selectbox(
                                        "🔎 Raio-X do Ativo selecionado:",
                                        options=opcoes_rx,
                                        key="raiox_ativo_sel",
                                    )
                                with c_rx2:
                                    st.markdown("<div style='padding-top:28px;'></div>", unsafe_allow_html=True)
                                    if st.button("✖️ Fechar Raio-X", key="btn_fechar_raiox", use_container_width=True):
                                        st.session_state["raiox_visivel"] = False
                                        st.rerun()

                                st.markdown(
                                    f"<span class='raiox-current-marker' id='raiox-current-{ativo_escolhido}' style='display:none;'></span>",
                                    unsafe_allow_html=True,
                                )
                                item_raiox = mapa_res[ativo_escolhido]
                                render_grafico_e_tabela_ativo(
                                    ativo_escolhido,
                                    item_raiox["nome"],
                                    base_ativo=item_raiox,
                                    key_prefix="tab1",
                                    modo_score_chave=modo_score_chave,
                                )

                            if idx_split + 1 < len(linhas_html):
                                st.markdown(
                                    f"<div class='val-table-wrap val-table-wrap-bot'><table class='val-table val-table-bot'><tbody>{''.join(linhas_html[idx_split + 1:])}</tbody></table></div>",
                                    unsafe_allow_html=True,
                                )

                    if idx_split is None:
                        st.markdown(
                            "<span class='raiox-current-marker' id='raiox-closed' style='display:none;'></span>",
                            unsafe_allow_html=True,
                        )

                render_tabela_e_raiox(
                    exibir,
                    [r["ticker"] for r in exibir],
                    {r["ticker"]: r for r in resultados_tab},
                    comp_set,
                    chave_score_ativo,
                )

        st.markdown("<div id='raiox'></div>", unsafe_allow_html=True)

        _usa_st_html = hasattr(st, "html") and "unsafe_allow_javascript" in inspect.signature(st.html).parameters
        _js_tabela = """
        <script>
        (function() {
            const pWin = __USE_PARENT__ ? window.parent : window;
            const pDoc = pWin.document;
            const STORAGE_KEY = "painel_b3_val_col_widths_v1";

            function sendBridgeInput(ariaLabel, payload) {
                const inp = pDoc.querySelector('input[aria-label="' + ariaLabel + '"]');
                if (!inp) return;
                const setter = Object.getOwnPropertyDescriptor(pWin.HTMLInputElement.prototype, "value").set;
                try { inp.focus({ preventScroll: true }); } catch (e) {}
                setter.call(inp, payload);
                inp.dispatchEvent(new Event("input", { bubbles: true }));
                inp.dispatchEvent(new Event("change", { bubbles: true }));
                setTimeout(function() {
                    const evInit = {
                        key: "Enter",
                        code: "Enter",
                        keyCode: 13,
                        which: 13,
                        bubbles: true,
                        cancelable: true
                    };
                    inp.dispatchEvent(new KeyboardEvent("keydown", evInit));
                    inp.dispatchEvent(new KeyboardEvent("keypress", evInit));
                    inp.dispatchEvent(new KeyboardEvent("keyup", evInit));
                    inp.dispatchEvent(new FocusEvent("blur", { bubbles: true }));
                }, 50);
            }

            pWin.__raioxSyncBridge = function(ticker) {
                const marker = pDoc.querySelector(".raiox-current-marker");
                const atual = marker && marker.id.startsWith("raiox-current-")
                    ? marker.id.replace("raiox-current-", "").trim().toUpperCase()
                    : "";
                const vaiFechar = (atual === ticker);
                pWin.__raioxPendingScroll = vaiFechar ? null : ticker;
                sendBridgeInput("raiox_bridge_input", ticker + "|" + Date.now());
            };

            pWin.__compSyncBridge = function(ticker) {
                sendBridgeInput("comp_bridge_input", ticker + "|" + Date.now());
            };

            function applyColgroupToTable(tbl, widthsArr, totW) {
                if (!tbl) return;
                let cg = tbl.querySelector("colgroup");
                if (!cg) {
                    cg = pDoc.createElement("colgroup");
                    tbl.insertBefore(cg, tbl.firstChild);
                }
                cg.innerHTML = "";
                widthsArr.forEach(function(w) {
                    const col = pDoc.createElement("col");
                    col.style.width = w + "px";
                    cg.appendChild(col);
                });
                tbl.style.tableLayout = "fixed";
                tbl.style.width = totW + "px";
                tbl.style.minWidth = totW + "px";
            }

            function syncWrapScroll() {
                const wrapTop = pDoc.querySelector(".val-table-wrap-top");
                const wrapBot = pDoc.querySelector(".val-table-wrap-bot");
                if (!wrapTop || !wrapBot) return;
                if (!wrapTop.dataset.scrollSync) {
                    wrapTop.dataset.scrollSync = "1";
                    wrapTop.addEventListener("scroll", function() {
                        if (wrapBot && wrapBot.scrollLeft !== wrapTop.scrollLeft) {
                            wrapBot.scrollLeft = wrapTop.scrollLeft;
                        }
                    });
                }
                if (!wrapBot.dataset.scrollSync) {
                    wrapBot.dataset.scrollSync = "1";
                    wrapBot.addEventListener("scroll", function() {
                        if (wrapTop && wrapTop.scrollLeft !== wrapBot.scrollLeft) {
                            wrapTop.scrollLeft = wrapBot.scrollLeft;
                        }
                    });
                }
            }

            pWin.__initValTableResize = function() {
                const topTable = pDoc.querySelector("table.val-table-top") || pDoc.querySelector("table.val-table");
                const botTable = pDoc.querySelector("table.val-table-bot");
                if (!topTable) return;
                const ths = Array.from(topTable.querySelectorAll("thead tr th"));
                if (!ths.length) return;

                syncWrapScroll();

                if (topTable.dataset.resizeReady && (!botTable || botTable.dataset.resizeReady)) return;

                let widths = [];
                let totalW = 0;

                if (topTable.dataset.resizeReady) {
                    const colsTop = Array.from(topTable.querySelectorAll("colgroup col"));
                    widths = colsTop.map(function(c, i) {
                        return Math.max(40, Math.round(parseFloat(c.style.width) || ths[i].getBoundingClientRect().width));
                    });
                    totalW = widths.reduce(function(a, b) { return a + b; }, 0);
                    if (botTable && !botTable.dataset.resizeReady) {
                        applyColgroupToTable(botTable, widths, totalW);
                        botTable.dataset.resizeReady = "1";
                    }
                    return;
                }

                let saved = {};
                try {
                    saved = JSON.parse(pWin.localStorage.getItem(STORAGE_KEY) || "{}") || {};
                } catch (err) {
                    saved = {};
                }
                const hasSaved = Object.keys(saved).length === ths.length;

                if (hasSaved) {
                    widths = ths.map((_, i) => Math.max(40, Number(saved[i]) || 90));
                } else {
                    topTable.style.tableLayout = "auto";
                    widths = ths.map((th, i) => Math.max(i === 0 ? 42 : 54, Math.round(th.getBoundingClientRect().width)));
                }

                totalW = widths.reduce((a, b) => a + b, 0);
                applyColgroupToTable(topTable, widths, totalW);
                widths.forEach((w, idx) => { ths[idx].style.width = w + "px"; });

                if (botTable) {
                    applyColgroupToTable(botTable, widths, totalW);
                    botTable.dataset.resizeReady = "1";
                }

                ths.forEach((th, idx) => {
                    if (th.querySelector(".col-resizer")) return;
                    const resizer = pDoc.createElement("div");
                    resizer.className = "col-resizer";
                    resizer.title = "Arraste para redimensionar (duplo clique para resetar)";

                    resizer.addEventListener("dblclick", function(ev) {
                        ev.preventDefault();
                        ev.stopPropagation();
                        try { pWin.localStorage.removeItem(STORAGE_KEY); } catch (e) {}
                        const bTbl = pDoc.querySelector("table.val-table-bot");
                        [topTable, bTbl].forEach(function(tbl) {
                            if (!tbl) return;
                            tbl.style.tableLayout = "auto";
                            tbl.style.width = "100%";
                            tbl.style.minWidth = "";
                            const cg = tbl.querySelector("colgroup");
                            if (cg) cg.remove();
                            delete tbl.dataset.resizeReady;
                        });
                        ths.forEach(function(t) { t.style.width = ""; });
                        setTimeout(pWin.__initValTableResize, 30);
                    });

                    resizer.addEventListener("mousedown", function(ev) {
                        ev.preventDefault();
                        ev.stopPropagation();
                        const startX = ev.clientX;
                        const cgCols = Array.from(topTable.querySelectorAll("colgroup col"));
                        const startW = cgCols[idx] ? parseFloat(cgCols[idx].style.width) : th.getBoundingClientRect().width;
                        const startTotalW = cgCols.reduce(function(acc, c) {
                            return acc + (parseFloat(c.style.width) || 80);
                        }, 0);
                        resizer.classList.add("resizing");
                        pDoc.body.style.cursor = "col-resize";

                        function onMove(mv) {
                            const delta = mv.clientX - startX;
                            const newW = Math.max(40, Math.round(startW + delta));
                            const diff = newW - startW;
                            const newTotal = Math.max(200, Math.round(startTotalW + diff));
                            if (cgCols[idx]) cgCols[idx].style.width = newW + "px";
                            th.style.width = newW + "px";
                            topTable.style.width = newTotal + "px";
                            topTable.style.minWidth = newTotal + "px";

                            const bTbl = pDoc.querySelector("table.val-table-bot");
                            if (bTbl) {
                                const bCols = Array.from(bTbl.querySelectorAll("colgroup col"));
                                if (bCols[idx]) bCols[idx].style.width = newW + "px";
                                bTbl.style.width = newTotal + "px";
                                bTbl.style.minWidth = newTotal + "px";
                            }
                        }

                        function onUp() {
                            resizer.classList.remove("resizing");
                            pDoc.body.style.cursor = "";
                            pDoc.removeEventListener("mousemove", onMove);
                            pDoc.removeEventListener("mouseup", onUp);
                            const obj = {};
                            const colsNow = Array.from(topTable.querySelectorAll("colgroup col"));
                            colsNow.forEach(function(c, i) {
                                obj[i] = Math.max(40, Math.round(parseFloat(c.style.width) || ths[i].getBoundingClientRect().width));
                            });
                            try {
                                pWin.localStorage.setItem(STORAGE_KEY, JSON.stringify(obj));
                            } catch (e) {}
                        }

                        pDoc.addEventListener("mousemove", onMove);
                        pDoc.addEventListener("mouseup", onUp);
                    });

                    th.appendChild(resizer);
                });

                topTable.dataset.resizeReady = "1";
            };

            pWin.__initValTableResize();

            if (!pWin.__valTableObserver) {
                pWin.__valTableObserver = new MutationObserver(function() {
                    if (pWin.__initValTableResize) {
                        pWin.__initValTableResize();
                    }
                    if (pWin.__raioxPendingScroll) {
                        const mk = pDoc.getElementById("raiox-current-" + pWin.__raioxPendingScroll);
                        if (mk) {
                            pWin.__raioxPendingScroll = null;
                            const activeRow = pDoc.querySelector("tr.raiox-active-row");
                            if (activeRow) {
                                setTimeout(function() {
                                    activeRow.scrollIntoView({ behavior: "smooth", block: "start" });
                                }, 80);
                            }
                        }
                    }
                });
                pWin.__valTableObserver.observe(pDoc.body, { childList: true, subtree: true });
            }

            if (!pWin.__raioxClickHandlerAttached) {
                pWin.__raioxClickHandlerAttached = true;
                pDoc.addEventListener("click", function(e) {
                    const chk = e.target && e.target.closest ? e.target.closest(".comp-chk-btn") : null;
                    if (chk) {
                        e.preventDefault();
                        e.stopPropagation();
                        chk.classList.toggle("checked");
                        chk.setAttribute("aria-checked", chk.classList.contains("checked") ? "true" : "false");
                        const tkCmp = (chk.getAttribute("data-comp-ticker") || "").trim().toUpperCase();
                        if (tkCmp && pWin.__compSyncBridge) {
                            pWin.__compSyncBridge(tkCmp);
                        }
                        return;
                    }

                    const tdCell = e.target && e.target.closest ? e.target.closest("table.val-table tbody tr td") : null;
                    if (tdCell && tdCell.cellIndex === 0) {
                        const innerChk = tdCell.querySelector(".comp-chk-btn");
                        if (innerChk) {
                            e.preventDefault();
                            e.stopPropagation();
                            innerChk.classList.toggle("checked");
                            innerChk.setAttribute("aria-checked", innerChk.classList.contains("checked") ? "true" : "false");
                            const tkCmp = (innerChk.getAttribute("data-comp-ticker") || "").trim().toUpperCase();
                            if (tkCmp && pWin.__compSyncBridge) {
                                pWin.__compSyncBridge(tkCmp);
                            }
                        }
                        return;
                    }

                    const rowRx = e.target && e.target.closest ? e.target.closest("table.val-table tbody tr[data-raiox-ticker]") : null;
                    if (rowRx) {
                        const selTxt = pWin.getSelection ? pWin.getSelection().toString() : "";
                        if (selTxt && selTxt.length > 0) return;
                        e.preventDefault();
                        e.stopPropagation();
                        const tickerRx = (rowRx.getAttribute("data-raiox-ticker") || "").trim().toUpperCase();
                        if (tickerRx && pWin.__raioxSyncBridge) {
                            pWin.__raioxSyncBridge(tickerRx);
                        }
                    }
                }, true);
            }
        })();
        </script>
        """.replace("__USE_PARENT__", "false" if _usa_st_html else "true")

        if _usa_st_html:
            st.html(_js_tabela, unsafe_allow_javascript=True)
        else:
            components.html(_js_tabela, height=0)

        # --- RANKING DE ATRATIVIDADE (EXPANDER + QUANTIDADE ESCOLHÍVEL) ---
        lista_rank_base = lista_tab if (busca_tabela and busca_tabela.strip() and lista_tab) else resultados_tab
        total_rank = len(lista_rank_base)
        with st.expander(f"🏆 Ranking de Atratividade (Filtro Atual — até {total_rank} ativos) — clique para minimizar/maximizar", expanded=True):
            if total_rank == 0:
                st.info("Nenhum ativo corresponde aos filtros de Veredito ou busca selecionados.")
            else:
                if total_rank > 1:
                    qtd_ranking = st.number_input(
                        f"Quantos ativos mostrar no Ranking (de 1 até {total_rank}):",
                        min_value=1,
                        max_value=total_rank,
                        value=min(100, total_rank),
                        step=10,
                        key="qtd_ranking_input",
                    )
                else:
                    qtd_ranking = total_rank

                blocos_ranking = []
                for r in lista_rank_base[:int(qtd_ranking)]:
                    score_at = r.get("score_ativo", r.get(chave_score_ativo, r["score_geral"]))
                    news_sc = float(r.get("news_score") or 0.0)
                    news_res = r.get("news_resumo", "⚪ Neutro")
                    quebra_txt = f"LP: **{r['score_lp']}** | CP: **{r['score_cp']}** | News: **{news_sc:+.1f}** ({news_res})"
                    faixa_txt = fmt_faixa_preco_modelo(r)
                    justificativa = "; ".join(r["motivos"]).capitalize() + "." if r["motivos"] else "Sem dados suficientes."
                    estrela = " ⭐" if r["ticker"] in st.session_state["favoritos"] else ""
                    blocos_ranking.append(
                        f"**{r['pos_ranking']}º Lugar: {r['ticker']}{estrela}** ({r['nome']}) | "
                        f"**Cotação: R$ {fmt_num(r['cotacao'])}** | "
                        f"**Score Ativo: {score_at}/100** | {r['veredito']}  \n"
                        f"📊 {quebra_txt}  \n"
                        f"🎯 Faixa do Modelo: {faixa_txt}  \n"
                        f"_{justificativa}_"
                    )
                st.markdown("\n\n".join(blocos_ranking))

        # --- SETOR DE ÚLTIMAS NOTÍCIAS E FATOS RELEVANTES (ABAIXO DO RANKING) ---
        ativos_para_news = exibir if exibir else lista_rank_base
        with st.expander("📰 Últimas Informações e Notícias dos Ativos Pesquisados / Filtrados — clique para minimizar/maximizar", expanded=True):
            limite_news = min(50, len(ativos_para_news))
            if limite_news > 1:
                if st.session_state.get("_last_limite_news") != limite_news:
                    st.session_state["qtd_news_input"] = limite_news
                    st.session_state["_last_limite_news"] = limite_news
                c_nw1, c_nw2 = st.columns([1.4, 2.6])
                with c_nw1:
                    qtd_news = st.number_input(
                        f"Buscar notícias para os primeiros N ativos (1 a {limite_news}):",
                        min_value=1,
                        max_value=limite_news,
                        value=limite_news,
                        step=1,
                        key="qtd_news_input",
                    )
                with c_nw2:
                    tks_news_opc = [r["ticker"] for r in ativos_para_news]
                    tks_news_sel = st.multiselect(
                        "Ou escolha ativos específicos da lista atual:",
                        options=tks_news_opc,
                        default=[],
                        key="ms_news_sel",
                    )
                alvo_news = tks_news_sel if tks_news_sel else [r["ticker"] for r in ativos_para_news[:int(qtd_news)]]
            else:
                alvo_news = [r["ticker"] for r in ativos_para_news]

            with st.spinner(f"Buscando últimas notícias no Google News para {len(alvo_news)} ativo(s)..."):
                noticias_dict = buscar_noticias_lote(tuple(alvo_news))

            mapa_nomes_tab = {r["ticker"]: r["nome"] for r in resultados}
            for t_n in alvo_news:
                lista_n = noticias_dict.get(t_n, [])
                nome_n = mapa_nomes_tab.get(t_n, t_n)
                st.markdown(f"**🗞️ {t_n}** — _{nome_n}_")
                if not lista_n:
                    st.caption("Nenhuma notícia recente encontrada no Google News para este código.")
                else:
                    for n_it in lista_n:
                        fonte_txt = f" · **{n_it['fonte']}**" if n_it["fonte"] else ""
                        dt_txt = f" ({n_it['data_str']})" if n_it["data_str"] else ""
                        st.markdown(f"- `{n_it['tag']}` [{n_it['titulo']}]({n_it['link']}){fonte_txt}{dt_txt}")
                st.markdown("---")

# ==================== ABA 2: COMPARAR ATIVOS ====================
with tab2:
    st.subheader("⚖️ Comparador Lado a Lado")
    if "ms_comp" not in st.session_state:
        default_comp = [r["ticker"] for r in resultados[:min(3, len(resultados))]] if resultados else tickers_b3[:3]
        st.session_state["ms_comp"] = default_comp
    selecionados = st.multiselect(
        "Escolha 2 ou mais ativos para comparar:",
        options=tickers_b3,
        key="ms_comp",
    )
    if st.session_state.get("comp_selecionados") or len(selecionados) != len(st.session_state.get("comp_selecionados", [])):
        if st.session_state.get("comp_selecionados"):
            st.session_state["comp_selecionados"] = list(selecionados)

    if len(selecionados) < 2:
        st.info("Selecione pelo menos 2 ativos acima para visualizar a comparação.")
    else:
        mapa_todos = {a["ticker"]: a for a in todos_ativos}
        mapa_res = {r["ticker"]: r for r in resultados}
        faltantes = tuple(t for t in selecionados if t not in dados_yf)
        extra_yf = buscar_yahoo_lote(faltantes) if faltantes else {}
        faltantes_nw = tuple(t for t in selecionados if t not in dados_news)
        if faltantes_nw:
            dados_news.update(buscar_sentimento_noticias_lote(faltantes_nw))

        itens_comp = []
        for t in selecionados:
            if t in mapa_res and t not in extra_yf and t not in faltantes_nw:
                itens_comp.append(mapa_res[t])
            else:
                dados_yf[t] = dados_yf.get(t) or extra_yf.get(t, {})
                it = montar_item_completo(mapa_todos[t])
                it["pos_ranking"] = mapa_res.get(t, {}).get("pos_ranking", "-")
                itens_comp.append(it)

        cols = st.columns(min(4, len(itens_comp)))
        for idx, r in enumerate(itens_comp):
            with cols[idx % len(cols)]:
                with st.container(border=True):
                    st.markdown(f"### {r['ticker']} ({r['pos_ranking']}º)")
                    st.caption(r["nome"])
                    st.metric("Cotação Atual", f"R$ {fmt_num(r['cotacao'])}", f"DY 12m: {fmt_num(r['dy_12m'])}%")
                    st.write(f"**Score:** {r['score']}/100")
                    pvp_txt = f"{fmt_num(r['pvp'])} {'🟢' if r['pvp'] < 1 else '🔴'}" if r["pvp"] is not None else "N/A"
                    pl_txt = fmt_num(r["pl"]) if r["pl"] is not None else "N/A"
                    roe_txt = f"{fmt_num(r['roe'], 1)}%" if r["roe"] is not None else "N/A"
                    st.write(f"**P/L:** {pl_txt} | **P/VP:** {pvp_txt} | **ROE:** {roe_txt}")
                    st.markdown("---")
                    st.markdown(f"**PT Médio (6a):** {html_preco_ms(r['pt_med'], r['cotacao'])}", unsafe_allow_html=True)
                    st.markdown(f"**PT Projetivo:** {html_preco_ms(r['pt_proj'], r['cotacao'])}", unsafe_allow_html=True)
                    st.markdown(f"**PT Bazin (12m):** {html_preco_ms(r['pt_bazin'], r['cotacao'])}", unsafe_allow_html=True)
                    st.markdown(f"**Graham:** {html_preco_ms(r['graham'], r['cotacao'])}", unsafe_allow_html=True)

        st.markdown("### 📈 Comparação de Rentabilidade (%) no Período")
        cp1, cp2 = st.columns([3, 1.2])
        with cp1:
            per_comp = st.radio("Período da comparação:", ["30 D", "6 M", "YTD", "1 A", "5 A", "10 A"], index=3, horizontal=True, key="comp_per")
        with cp2:
            tipo_comp = st.selectbox("Tipo:", ["Cotação ajustada", "Cotação simples"], index=0, key="comp_tipo")

        fig_comp = go.Figure()
        for r in itens_comp:
            s = buscar_historico_preco(r["ticker"], per_comp, tipo_comp == "Cotação ajustada")
            if not s.empty and float(s.iloc[0]) > 0:
                pct = ((s / float(s.iloc[0])) - 1.0) * 100
                fig_comp.add_trace(
                    go.Scatter(
                        x=pct.index, y=pct.values, mode="lines", name=f"{r['ticker']} ({pct.iloc[-1]:+.1f}%)",
                        hovertemplate=f"<b>{r['ticker']}</b><br>%{{x|%d/%m/%Y}}: %{{y:+.2f}}%<extra></extra>",
                    )
                )
        fig_comp.update_layout(
            height=340, margin=dict(l=10, r=10, t=20, b=15),
            paper_bgcolor="rgba(0,0,0,0)", plot_bgcolor="rgba(0,0,0,0)",
            hovermode="x unified",
            yaxis=dict(showgrid=True, gridcolor="rgba(128,128,128,0.25)", ticksuffix="%"),
            xaxis=dict(showgrid=False),
            legend=dict(orientation="h", yanchor="bottom", y=1.02, xanchor="left", x=0),
        )
        st.plotly_chart(fig_comp, use_container_width=True)

        st.markdown("### 🔍 Gráfico Individual e Histórico Fundamentalista dos Ativos Comparados")
        subtabs = st.tabs([f"📊 {r['ticker']}" for r in itens_comp])
        for st_tab, r in zip(subtabs, itens_comp):
            with st_tab:
                render_grafico_e_tabela_ativo(r["ticker"], r["nome"], base_ativo=r, key_prefix="comp_sub")

# ==================== ABA 3: MINHA CARTEIRA (PROTEGIDA POR LOGIN) ====================
with tab3:
    if not usuario_atual:
        render_tela_login(key_prefix="tab_cart")
    else:
        c_head, c_btn_top = st.columns([3.5, 1.3])
        with c_head:
            st.subheader(f"💼 Minha Carteira — {usuario_atual}")
        with c_btn_top:
            if st.button("➕ Adicionar Lançamento", type="primary", use_container_width=True, key="btn_add_top"):
                modal_adicionar_lancamento(tickers_b3)

        if not posicoes_carteira:
            st.info("Sua carteira ainda está vazia. Clique em **➕ Adicionar Lançamento** ali em cima para cadastrar seu primeiro ativo!")
        else:
            mapa_todos = {a["ticker"]: a for a in todos_ativos}
            tickers_cart = tuple(posicoes_carteira.keys())
            faltantes_c = tuple(t for t in tickers_cart if t not in dados_yf)
            if faltantes_c:
                dados_yf.update(buscar_yahoo_lote(faltantes_c))
            faltantes_cn = tuple(t for t in tickers_cart if t not in dados_news)
            if faltantes_cn:
                dados_news.update(buscar_sentimento_noticias_lote(faltantes_cn))

            hist_cart = buscar_divs_e_precos_carteira(tickers_cart)
            mapa_setores_full = carregar_mapa_todos_setores()

            hoje_dt = pd.Timestamp.now().tz_localize(None)
            inicio_12m_dt = hoje_dt - timedelta(days=365)

            total_investido = 0.0
            total_atual = 0.0
            divs_total_recebidos = 0.0
            divs_12m_recebidos = 0.0
            itens_tabela_cart = []
            valor_por_setor: dict[str, float] = {}

            for t, pos in posicoes_carteira.items():
                base = mapa_todos.get(t)
                if not base:
                    yf_b = dados_yf.get(t, {})
                    cot_fb = yf_b.get("cotacao_yf")
                    if not cot_fb:
                        px_s = hist_cart.get(t, {}).get("px", pd.Series(dtype=float))
                        cot_fb = float(px_s.iloc[-1]) if not px_s.empty else pos["pm"]
                    base = {"ticker": t, "cotacao": cot_fb, "pl": None, "pvp": None, "roe": None, "lpa": None, "vpa": None, "dpa_12m": 0.0, "dy_12m": 0.0}

                item_val = montar_item_completo(base)
                cot = item_val["cotacao"]
                qtd = pos["qtd"]
                pm = pos["pm"]
                inv = pos["custo"]
                saldo = qtd * cot
                ganho_cap = saldo - inv

                divs_serie = hist_cart.get(t, {}).get("divs", pd.Series(dtype=float))
                lanc_t = sorted([l for l in st.session_state["lancamentos"] if l["ticker"] == t], key=lambda x: x["data"])
                div_ativo_tot = 0.0
                div_ativo_12m = 0.0

                if not divs_serie.empty and lanc_t:
                    for dt_div, dpa_val in divs_serie.items():
                        qtd_na_data = 0.0
                        for l in lanc_t:
                            if pd.to_datetime(l["data"]) <= dt_div:
                                qtd_na_data += l["qtd"] if l.get("tipo", "C") == "C" else -l["qtd"]
                        if qtd_na_data > 0:
                            recebido = qtd_na_data * float(dpa_val)
                            div_ativo_tot += recebido
                            if dt_div >= inicio_12m_dt:
                                div_ativo_12m += recebido

                var_pct = ((cot / pm) - 1) * 100 if pm > 0 else 0.0
                rent_pct = (((saldo + div_ativo_tot) / inv) - 1) * 100 if inv > 0 else 0.0

                total_investido += inv
                total_atual += saldo
                divs_total_recebidos += div_ativo_tot
                divs_12m_recebidos += div_ativo_12m

                setor_t = mapa_setores_full.get(t, pos.get("tipo_ativo", "Outros"))
                valor_por_setor[setor_t] = valor_por_setor.get(setor_t, 0.0) + saldo

                itens_tabela_cart.append({
                    **item_val,
                    "qtd": qtd, "pm": pm, "inv": inv, "saldo": saldo,
                    "ganho_cap": ganho_cap, "div_tot": div_ativo_tot,
                    "var_pct": var_pct, "rent_pct": rent_pct, "setor_t": setor_t,
                })

            meses = pd.date_range(end=hoje_dt, periods=12, freq="ME").tolist()
            if not meses or meses[-1].month != hoje_dt.month or meses[-1].year != hoje_dt.year:
                meses = (meses + [hoje_dt])[-12:]

            labels_mes, vals_aplicado, vals_ganho = [], [], []
            lanc_ord = sorted(st.session_state["lancamentos"], key=lambda x: x["data"])

            for idx_m, dt_m in enumerate(meses):
                eh_atual = (idx_m == len(meses) - 1)
                labels_mes.append(dt_m.strftime("%m/%y"))

                pos_m: dict[str, dict] = {}
                for l in lanc_ord:
                    if pd.to_datetime(l["data"]) <= dt_m:
                        t = l["ticker"]
                        if t not in pos_m:
                            pos_m[t] = {"qtd": 0.0, "custo": 0.0, "pm": 0.0}
                        custos = float(l.get("custos", 0.0) or 0.0)
                        if l.get("tipo", "C") == "C":
                            pos_m[t]["qtd"] += l["qtd"]
                            pos_m[t]["custo"] += (l["qtd"] * l["preco"]) + custos
                            pos_m[t]["pm"] = pos_m[t]["custo"] / pos_m[t]["qtd"] if pos_m[t]["qtd"] > 0 else 0.0
                        else:
                            qv = min(pos_m[t]["qtd"], l["qtd"])
                            pos_m[t]["qtd"] -= qv
                            pos_m[t]["custo"] = pos_m[t]["qtd"] * pos_m[t]["pm"]

                ap_m = sum(v["custo"] for v in pos_m.values() if v["qtd"] > 0)
                sal_m = 0.0
                for t, v in pos_m.items():
                    if v["qtd"] <= 0:
                        continue
                    if eh_atual and t in mapa_todos:
                        px_m = mapa_todos[t]["cotacao"]
                    else:
                        px_ser = hist_cart.get(t, {}).get("px", pd.Series(dtype=float))
                        sub_px = px_ser[px_ser.index <= dt_m] if not px_ser.empty else pd.Series(dtype=float)
                        px_m = float(sub_px.iloc[-1]) if not sub_px.empty else v["pm"]
                    sal_m += v["qtd"] * px_m

                vals_aplicado.append(ap_m)
                vals_ganho.append(sal_m - ap_m)

            ganho_cap_tot = total_atual - total_investido
            lucro_total = ganho_cap_tot + divs_total_recebidos
            var_cart_pct = ((total_atual / total_investido) - 1) * 100 if total_investido > 0 else 0.0
            rent_total_pct = ((lucro_total / total_investido) * 100) if total_investido > 0 else 0.0

            k1, k2, k3, k4 = st.columns(4)
            with k1:
                with st.container(border=True):
                    cor_v = "#22c55e" if var_cart_pct >= 0 else "#ef4444"
                    st.caption("💼 Patrimônio total")
                    st.markdown(f"<span style='font-size:24px; font-weight:700;'>R$ {fmt_num(total_atual)}</span> <span style='color:{cor_v}; font-weight:600;'>{var_cart_pct:+.2f}%</span>", unsafe_allow_html=True)
                    st.caption(f"Valor investido: **R$ {fmt_num(total_investido)}**")
            with k2:
                with st.container(border=True):
                    cor_l = "#22c55e" if lucro_total >= 0 else "#ef4444"
                    st.caption("💰 Lucro total")
                    st.markdown(f"<span style='font-size:24px; font-weight:700; color:{cor_l};'>R$ {fmt_num(lucro_total)}</span>", unsafe_allow_html=True)
                    st.caption(f"Ganho Cap: **R$ {fmt_num(ganho_cap_tot)}** | Divs: **R$ {fmt_num(divs_total_recebidos)}**")
            with k3:
                with st.container(border=True):
                    st.caption("💵 Proventos Recebidos (12M)")
                    st.markdown(f"<span style='font-size:24px; font-weight:700;'>R$ {fmt_num(divs_12m_recebidos)}</span>", unsafe_allow_html=True)
                    st.caption(f"Total recebido desde compras: **R$ {fmt_num(divs_total_recebidos)}**")
            with k4:
                with st.container(border=True):
                    cor_r = "#22c55e" if rent_total_pct >= 0 else "#ef4444"
                    st.caption("📈 Rentabilidade (c/ dividendos)")
                    st.markdown(f"<span style='font-size:24px; font-weight:700; color:{cor_r};'>{rent_total_pct:+.2f}%</span>", unsafe_allow_html=True)
                    st.caption(f"Variação pura do preço: **{var_cart_pct:+.2f}%**")

            g_esq, g_dir = st.columns([1.8, 1])
            with g_esq:
                with st.container(border=True):
                    st.markdown("**Evolução do Patrimônio (Últimos 12 Meses)**")
                    fig_ev = go.Figure()
                    fig_ev.add_trace(go.Bar(
                        x=labels_mes, y=vals_aplicado, name="Valor aplicado",
                        marker_color="#10b981", hovertemplate="Valor aplicado: R$ %{y:,.2f}<extra></extra>",
                    ))
                    fig_ev.add_trace(go.Bar(
                        x=labels_mes, y=vals_ganho, name="Ganho de Capital",
                        marker_color=["#6ee7b7" if g >= 0 else "#fca5a5" for g in vals_ganho],
                        hovertemplate="Ganho de Capital: R$ %{y:,.2f}<extra></extra>",
                    ))
                    fig_ev.update_layout(
                        barmode="relative", height=290, margin=dict(l=10, r=10, t=25, b=10),
                        paper_bgcolor="rgba(0,0,0,0)", plot_bgcolor="rgba(0,0,0,0)",
                        yaxis=dict(showgrid=True, gridcolor="rgba(128,128,128,0.22)", tickprefix="R$ "),
                        xaxis=dict(showgrid=False),
                        legend=dict(orientation="h", yanchor="bottom", y=1.02, xanchor="center", x=0.5),
                    )
                    st.plotly_chart(fig_ev, use_container_width=True)

            with g_dir:
                with st.container(border=True):
                    modo_pizza = st.selectbox("Ativos na Carteira:", ["Por Ativo", "Por Setor"], index=0, label_visibility="collapsed")
                    if modo_pizza == "Por Ativo":
                        lbls = [x["ticker"] for x in itens_tabela_cart]
                        vals = [x["saldo"] for x in itens_tabela_cart]
                    else:
                        lbls = list(valor_por_setor.keys())
                        vals = list(valor_por_setor.values())
                    fig_pz = go.Figure(data=[go.Pie(labels=lbls, values=vals, hole=0.52, textinfo="label+percent")])
                    fig_pz.update_layout(
                        title=f"Ativos na Carteira ({modo_pizza})",
                        height=245, margin=dict(l=10, r=10, t=35, b=10),
                        paper_bgcolor="rgba(0,0,0,0)", showlegend=False,
                    )
                    st.plotly_chart(fig_pz, use_container_width=True)

            itens_tabela_cart.sort(key=lambda x: x["saldo"], reverse=True)
            st.markdown(
                f"#### 📋 Ações ({len(itens_tabela_cart)} ativos) — "
                f"Valor total: **R$ {fmt_num(total_atual)}** | Variação: **{var_cart_pct:+.2f}%** | Rentabilidade: **{rent_total_pct:+.2f}%**"
            )

            rows_c = []
            base_params_c = {"liq": liq_label}
            if len(filtro_setores) == 1:
                base_params_c["setor"] = filtro_setores[0]
            for r in itens_tabela_cart:
                cot = r["cotacao"]
                pct_cart = (r["saldo"] / total_atual * 100) if total_atual > 0 else 0.0
                cor_var = "#22c55e" if r["var_pct"] >= 0 else "#ef4444"
                cor_rent = "#22c55e" if r["rent_pct"] >= 0 else "#ef4444"

                pl_txt = fmt_num(r["pl"]) if r["pl"] is not None else "N/A"
                if r["pvp"] is not None:
                    cor_pvp = "#22c55e" if r["pvp"] < 1 else "#ef4444"
                    pvp_html = f"<span style='color:{cor_pvp}; font-weight:600;'>{fmt_num(r['pvp'])} {'🟢' if r['pvp'] < 1 else '🔴'}</span>"
                else:
                    pvp_html = "N/A"
                roe_txt = f"{fmt_num(r['roe'], 1)}%" if r["roe"] is not None else "N/A"
                lpa_txt = f"R$ {fmt_num(r['lpa'])}" if r["lpa"] is not None else "N/A"
                vpa_txt = f"R$ {fmt_num(r['vpa'])}" if r["vpa"] is not None else "N/A"
                dpa6_txt = f"R$ {fmt_num(r['dpa_med_6a'])}" if r["dpa_med_6a"] is not None else "—"
                dpap_txt = f"R$ {fmt_num(r['dpa_proj'])}" if r["dpa_proj"] is not None else "—"
                sufixo_6a = "*" if 0 < r["anos_hist"] < 6 else ""

                href_c = f"?{urlencode({**base_params_c, 'ativo': r['ticker']})}#raiox"
                qtd_fmt = int(r["qtd"]) if float(r["qtd"]).is_integer() else r["qtd"]

                rows_c.append(
                    "<tr>"
                    f"<td><a href='{href_c}' target='_self' style='color:#60a5fa; text-decoration:none; font-weight:700;'>🔎 {r['ticker']}</a><br><small style='opacity:0.75;'>{html.escape(r['setor_t'])}</small><br><small>Score: <strong>{r['score']}</strong></small></td>"
                    f"<td>Qtd: <strong>{qtd_fmt}</strong><br>PM: R$ {fmt_num(r['pm'])}<br>Atual: <strong>R$ {fmt_num(cot)}</strong></td>"
                    f"<td>Saldo: <strong>R$ {fmt_num(r['saldo'])}</strong><br>Peso: {fmt_num(pct_cart, 1)}%<br>Var: <span style='color:{cor_var}; font-weight:600;'>{r['var_pct']:+.2f}%</span> | Rent: <span style='color:{cor_rent}; font-weight:600;'>{r['rent_pct']:+.2f}%</span></td>"
                    f"<td>P/L: {pl_txt}<br>P/VP: {pvp_html}<br>ROE: {roe_txt} | DY: {fmt_num(r['dy_12m'])}%</td>"
                    f"<td>LPA: {lpa_txt} | VPA: {vpa_txt}<br>12m: R$ {fmt_num(r['dpa_12m'])} | 6a: {dpa6_txt}<br>Proj: {dpap_txt}</td>"
                    f"<td>{html_preco_ms(r['pt_med'], cot, sufixo_6a)}</td>"
                    f"<td>{html_preco_ms(r['pt_proj'], cot)}</td>"
                    f"<td>{html_preco_ms(r['pt_bazin'], cot)}</td>"
                    f"<td>{html_preco_ms(r['graham'], cot)}</td>"
                    "</tr>"
                )

            css_c = (
                "<style>"
                ".cart-wrap{width:100%;overflow-x:auto;}"
                ".cart-table{width:100%;border-collapse:collapse;font-size:13px;line-height:1.4;}"
                ".cart-table th{background-color:rgba(128,128,128,0.18);text-align:left;padding:8px 6px;border-bottom:2px solid rgba(128,128,128,0.35);font-weight:600;font-size:12px;}"
                ".cart-table td{padding:8px 6px;border-bottom:1px solid rgba(128,128,128,0.22);vertical-align:middle;}"
                ".cart-table tr:hover td{background-color:rgba(128,128,128,0.08);}"
                "</style>"
            )
            html_c = (
                f"{css_c}<div class='cart-wrap'><table class='cart-table'><thead><tr>"
                "<th>Ativo / Setor</th><th>Posição<br><small>(Qtd | PM | Atual)</small></th>"
                "<th>Saldo & Retorno<br><small>(Peso | Var. | Rent.)</small></th>"
                "<th>Indicadores<br><small>(P/L | P/VP | ROE | DY)</small></th>"
                "<th>Dados Base<br><small>(LPA | VPA | DPAs)</small></th>"
                "<th>PT Médio (6a) & MS</th><th>PT Projetivo & MS</th>"
                "<th>PT Bazin (12m) & MS</th><th>Graham & MS</th>"
                f"</tr></thead><tbody>{''.join(rows_c)}</tbody></table></div>"
            )
            st.markdown(html_c, unsafe_allow_html=True)

            with st.expander("🔎 Abrir Gráfico & Histórico Fundamentalista de um ativo da carteira", expanded=False):
                tk_c_sel = st.selectbox("Escolha o ativo da carteira:", options=[x["ticker"] for x in itens_tabela_cart], key="cart_raiox_sel")
                it_c_sel = next(x for x in itens_tabela_cart if x["ticker"] == tk_c_sel)
                render_grafico_e_tabela_ativo(tk_c_sel, it_c_sel["nome"], base_ativo=it_c_sel, key_prefix="cart_rx")

        st.markdown("---")
        c_l1, c_l2 = st.columns([3.5, 1.3])
        with c_l2:
            if st.button("➕ Adicionar Lançamento", type="primary", use_container_width=True, key="btn_add_bot"):
                modal_adicionar_lancamento(tickers_b3)

        with c_l1:
            with st.expander(f"🧾 Lançamentos ({len(st.session_state['lancamentos'])}) & Backup CSV", expanded=False):
                if st.session_state["lancamentos"]:
                    df_l = pd.DataFrame(st.session_state["lancamentos"])
                    st.dataframe(df_l, use_container_width=True)
                    c_del, c_limp, c_dl = st.columns([2, 1, 1.2])
                    with c_del:
                        op_del = [
                            f"{i}: {x['data']} | {'Compra' if x['tipo']=='C' else 'Venda'} {x['qtd']:g} {x['ticker']} @ R$ {x['preco']:.2f}"
                            for i, x in enumerate(st.session_state["lancamentos"])
                        ]
                        esc_del = st.selectbox("Excluir lançamento:", ["—"] + op_del)
                        if esc_del != "—" and st.button("🗑️ Excluir"):
                            idx_d = int(esc_del.split(":")[0])
                            st.session_state["lancamentos"].pop(idx_d)
                            salvar_dados_usuario_nuvem()
                            st.rerun()
                    with c_limp:
                        if st.button("🧹 Limpar Tudo"):
                            st.session_state["lancamentos"] = []
                            salvar_dados_usuario_nuvem()
                            st.rerun()
                    with c_dl:
                        st.download_button(
                            "📥 Baixar CSV",
                            data=df_l.to_csv(index=False).encode("utf-8"),
                            file_name="lancamentos_carteira_b3.csv",
                            mime="text/csv",
                            use_container_width=True,
                        )

                arq = st.file_uploader("📤 Importar Backup CSV (colunas: ticker, qtd, preco, data, tipo, custos):", type=["csv"])
                if arq is not None:
                    try:
                        df_imp = pd.read_csv(io.BytesIO(arq.getvalue()))
                        if {"ticker", "qtd"}.issubset(df_imp.columns):
                            lista_imp = []
                            hoje_iso = datetime.now(BRT).strftime("%Y-%m-%d")
                            for _, row in df_imp.iterrows():
                                t = str(row["ticker"]).strip().upper().replace(".SA", "")
                                px_val = float(row["preco"]) if "preco" in df_imp.columns else float(row.get("pm", 0))
                                ct_val = float(row["custos"]) if "custos" in df_imp.columns and pd.notna(row["custos"]) else 0.0
                                dt_val = str(row["data"]) if "data" in df_imp.columns and pd.notna(row["data"]) else hoje_iso
                                tp_val = str(row["tipo"]) if "tipo" in df_imp.columns and str(row["tipo"]) in ("C", "V") else "C"
                                ta_val = str(row["tipo_ativo"]) if "tipo_ativo" in df_imp.columns and pd.notna(row["tipo_ativo"]) else "Ações"
                                if t:
                                    lista_imp.append({"ticker": t, "tipo_ativo": ta_val, "qtd": float(row["qtd"]), "preco": px_val, "custos": ct_val, "data": dt_val, "tipo": tp_val})
                            st.session_state["lancamentos"] = lista_imp
                            salvar_dados_usuario_nuvem()
                            st.success("Lançamentos importados e salvos na sua conta!")
                            st.rerun()
                    except Exception as exc:
                        st.error(f"Arquivo inválido: {exc}")

st.divider()
st.caption("Aviso: Estudo quantitativo e educacional com dados obtidos via Fundamentus, CVM Dados Abertos e Yahoo Finance. Não constitui recomendação oficial de compra ou venda.")
