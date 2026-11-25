import hashlib
import hmac
import html
import io
import json
import math
import re
import secrets
import xml.etree.ElementTree as ET
import zipfile
from concurrent.futures import ThreadPoolExecutor
from datetime import date, datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from urllib.parse import urlencode

import pandas as pd
import plotly.graph_objects as go
import requests
import streamlit as st
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


# --- NOTÍCIAS (GOOGLE NEWS RSS PT-BR) ---
def _classificar_noticia(titulo: str) -> str:
    t = titulo.lower()
    if any(k in t for k in ("prejuízo", "prejuizo", "queda", "cai ", "desaba", "rombo", "crise", "investiga", "multa", "inadimpl", "calote", "rebaix")):
        return "🔴 Atenção"
    if any(k in t for k in ("privatiz", "leilão", "leilao", "fusão", "fusao", "aquisição", "aquisicao", "compra ", "venda ", "fato relevante", "estatiz", "governo", "desestatiz")):
        return "🏛️ Fato/Corporativo"
    if any(k in t for k in ("lucro", "dividendo", "jcp", "provento", "recorde", "dispara", "sobe ", "alta ", "aprova", "supera")):
        return "🟢 Positivo/Provento"
    return "📰 Notícia"


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
                        itens.append({
                            "titulo": titulo, "link": link, "fonte": fonte,
                            "data_str": dt_str, "tag": _classificar_noticia(titulo),
                            "ts": dt_obj.timestamp() if dt_obj else 0.0,
                        })
                if itens:
                    itens.sort(key=lambda x: x["ts"], reverse=True)
                    return ticker, itens[:5]
            except Exception:
                continue
        return ticker, []

    out = {}
    if not tickers_tuple:
        return out
    with ThreadPoolExecutor(max_workers=8) as ex:
        for t, res in ex.map(_one, tickers_tuple):
            out[t] = res
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


def _ler_tabela_fundamentus(url: str) -> list[dict]:
    resp = requests.get(url, headers=HEADERS, timeout=20)
    resp.raise_for_status()
    soup = BeautifulSoup(resp.text, "lxml")
    tabela = soup.find("table", {"id": "resultado"})
    if not tabela:
        return []
    cabecalho = [th.get_text(strip=True) for th in tabela.find("thead").find_all("th")]
    registros = []
    for tr in tabela.find("tbody").find_all("tr"):
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
                "rec": _ttm_flow("rec"),
                "lbr": _ttm_flow("lbr"),
                "lliq": _ttm_flow("lliq"),
                "ebitda": ebitda_ttm,
                "patr": met_curr.get("patr"),
                "div_liq": met_curr.get("div_liq"),
            }

    return anuais, ttm_cvm


@st.cache_data(ttl=1800, show_spinner=False)
def carregar_todos_ativos_b3() -> list[dict]:
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

        lpa = (cotacao / pl) if (pl is not None and pl != 0) else None
        vpa = (cotacao / pvp) if (pvp is not None and pvp != 0) else None
        dpa_12m = cotacao * (dy / 100.0)

        ativos.append({
            "ticker": papel, "nome": papel, "cotacao": cotacao, "dy_12m": dy,
            "pl": pl, "pvp": pvp, "roe": roe, "lpa": lpa, "vpa": vpa,
            "dpa_12m": dpa_12m, "liq_2m": liq_2m,
        })
    return ativos


@st.cache_data(ttl=3600, show_spinner=False)
def carregar_tickers_por_setor(setor_ids: tuple[str, ...]) -> dict[str, str]:
    mapa_setor = {}
    setores_dict = carregar_setores_fundamentus()
    id_para_nome = {v: k for k, v in setores_dict.items()}
    for sid in setor_ids:
        linhas = _ler_tabela_fundamentus(f"https://www.fundamentus.com.br/resultado.php?setor={sid}")
        nome_setor = id_para_nome.get(sid, f"Setor {sid}")
        for row in linhas:
            papel = row.get("Papel", "").strip().upper()
            if papel:
                mapa_setor[papel] = nome_setor
    return mapa_setor


@st.cache_data(ttl=86400, show_spinner=False)
def carregar_mapa_todos_setores() -> dict[str, str]:
    setores_dict = carregar_setores_fundamentus()
    return carregar_tickers_por_setor(tuple(setores_dict.values()))


def _fetch_yf(ticker: str) -> tuple[str, dict]:
    try:
        tk = yf.Ticker(f"{ticker}.SA")
        info = tk.info or {}
        nome_raw = info.get("shortName") or info.get("longName") or ticker
        nome = " ".join(nome_raw.split())

        cot_yf = info.get("currentPrice") or info.get("regularMarketPrice")
        if not cot_yf:
            h5 = tk.history(period="5d")
            if h5 is not None and not h5.empty:
                cot_yf = float(h5["Close"].iloc[-1])

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
        }
    except Exception:
        return ticker, {}


@st.cache_data(ttl=1800, show_spinner=False)
def buscar_yahoo_lote(tickers_tuple: tuple[str, ...]) -> dict[str, dict]:
    if not tickers_tuple:
        return {}
    resultados = {}
    with ThreadPoolExecutor(max_workers=8) as executor:
        for ticker, dados in executor.map(_fetch_yf, tickers_tuple):
            resultados[ticker] = dados
    return resultados


@st.cache_data(ttl=900, show_spinner=False)
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


@st.cache_data(ttl=3600, show_spinner=False)
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
    acoes_info = acoes_fund or info.get("sharesOutstanding")
    cot_fund = parse_br_num(det_fund.get("Cotação"))
    cot_atual = cot_live or cot_fund or info.get("currentPrice") or info.get("regularMarketPrice")
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
    pl_12 = parse_br_num(det_fund.get("P/L")) or pl_live
    pvp_12 = parse_br_num(det_fund.get("P/VP")) or pvp_live
    val_merc_12 = val_merc_fund or ((cot_atual * acoes_info) if (cot_atual and acoes_info) else info.get("marketCap"))
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

    linhas.append({
        "ano": f"ATUAL{cot_txt}",
        "pl": pl_atual,
        "pvp": pvp_atual,
        "vpa": vpa_live if vpa_live is not None else vpa_12,
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


def render_grafico_e_tabela_ativo(ticker: str, nome: str = "", base_ativo: dict | None = None, key_prefix: str = "raiox"):
    c_tit, c_fav = st.columns([4, 1.3])
    eh_fav = ticker in st.session_state["favoritos"]
    with c_tit:
        st.markdown(f"### 📈 COTAÇÃO {ticker} {f'— {nome}' if nome and nome != ticker else ''}")
    with c_fav:
        lbl_fav = "★ Remover dos Favoritos" if eh_fav else "⭐ Adicionar aos Favoritos"
        if st.button(lbl_fav, key=f"{key_prefix}_favbtn_{ticker}", use_container_width=True):
            toggle_favorito(ticker)
            st.rerun()

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
        for h in hist_fund:
            pl_s = fmt_num(h["pl"]) if h["pl"] is not None else "—"
            pvp_s = fmt_num(h["pvp"]) if h["pvp"] is not None else "—"
            vpa_s = fmt_num(h["vpa"]) if h["vpa"] is not None else "—"
            ml_s = f"{fmt_num(h['marg_liq'])}%" if h["marg_liq"] is not None else "—"
            peb_s = fmt_num(h["pebitda"]) if h["pebitda"] is not None else "—"
            estilo_row = "background-color:rgba(96,165,250,0.14); font-weight:700;" if h.get("is_atual") else ""
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
        st.caption(f"Nota: {nota_src}{nota_b}")


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


def calcular_score(d: dict, pt_med: float | None, pt_proj: float | None, pt_bazin: float | None, graham: float | None) -> tuple[float, float | None, list[str]]:
    cot = d["cotacao"]
    ms_lista = [x for x in [calc_ms(pt_med, cot), calc_ms(pt_proj, cot), calc_ms(pt_bazin, cot), calc_ms(graham, cot)] if x is not None]

    if ms_lista:
        ms_limitadas = [max(-40.0, min(60.0, m)) for m in ms_lista]
        avg_ms_lim = sum(ms_limitadas) / len(ms_limitadas)
        avg_ms_real = sum(ms_lista) / len(ms_lista)
        pts_ms = max(0.0, min(45.0, ((avg_ms_lim + 40.0) / 100.0) * 45.0))
    else:
        avg_ms_real = None
        pts_ms = 0.0

    pvp = d["pvp"]
    pts_pvp = (max(0.0, min(15.0, ((2.5 - pvp) / 1.5) * 15.0)) + (5.0 if pvp < 1.0 else 0.0)) if (pvp and pvp > 0) else 0.0
    pl = d["pl"]
    pts_pl = max(0.0, min(15.0, ((20.0 - pl) / 15.0) * 15.0)) if (pl and pl > 0) else 0.0
    roe = d["roe"]
    pts_roe = min(20.0, (roe / 25.0) * 20.0) if (roe and roe > 0) else 0.0

    score = round(pts_ms + pts_pvp + pts_pl + pts_roe, 1)

    motivos = []
    if avg_ms_real is not None:
        if avg_ms_real > 15:
            motivos.append(f"forte desconto médio ({avg_ms_real:+.1f}%) nos métodos")
        elif avg_ms_real > 0:
            motivos.append(f"margem de segurança média positiva ({avg_ms_real:+.1f}%)")
        else:
            motivos.append(f"negociada acima da média dos preços-teto ({avg_ms_real:+.1f}%)")
    if pvp is not None:
        if pvp < 1:
            motivos.append(f"P/VP descontado ({fmt_num(pvp)})")
        elif pvp > 1.8:
            motivos.append(f"P/VP esticado ({fmt_num(pvp)})")
    if roe is not None:
        if roe >= 15:
            motivos.append(f"ROE forte ({fmt_num(roe, 1)}%)")
        elif roe < 8:
            motivos.append(f"ROE baixo ({fmt_num(roe, 1)}%)")
    if pl is not None and pl < 0:
        motivos.append("atenção: lucro negativo")

    return score, avg_ms_real, motivos


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

    opcoes_filtro = [
        "Todos os Ativos da B3",
        "🌟 BESST (Bancos, Energia, Saneamento, Seguros e Telecom)",
        "⭐ Apenas Meus Favoritos",
        "💼 Apenas Minha Carteira",
    ] + sorted(setores_dict.keys())

    setor_url = st.query_params.get("setor", "Todos os Ativos da B3")
    idx_setor = opcoes_filtro.index(setor_url) if setor_url in opcoes_filtro else 0
    filtro_setor = st.selectbox("Filtrar por Setor:", opcoes_filtro, index=idx_setor)

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
    if "ms_favs" not in st.session_state:
        st.session_state["ms_favs"] = [f for f in st.session_state["favoritos"] if f in tickers_b3]
    favs_sel = st.multiselect("Selecione suas favoritas:", options=tickers_b3, key="ms_favs")
    if favs_sel != st.session_state["favoritos"]:
        st.session_state["favoritos"] = favs_sel
        salvar_dados_usuario_nuvem()
        st.rerun()

    if st.button("🔄 Atualizar Dados", type="primary", use_container_width=True):
        st.cache_data.clear()
        st.rerun()

st.query_params["setor"] = filtro_setor
st.query_params["liq"] = liq_label
if busca_tickers.strip():
    st.query_params["busca"] = busca_tickers.strip()
elif "busca" in st.query_params:
    del st.query_params["busca"]

posicoes_carteira = consolidar_carteira_por_ativo(st.session_state["lancamentos"]) if usuario_atual else {}

mapa_setores_ativos = {}
ativos_filtrados = todos_ativos

if filtro_setor == "🌟 BESST (Bancos, Energia, Saneamento, Seguros e Telecom)":
    ids_besst = tuple(setores_dict[s] for s in BESST_SETORES if s in setores_dict)
    if ids_besst:
        with st.spinner("Filtrando empresas do setor BESST..."):
            mapa_setores_ativos = carregar_tickers_por_setor(ids_besst)
        ativos_filtrados = [a for a in todos_ativos if a["ticker"] in mapa_setores_ativos]
elif filtro_setor == "⭐ Apenas Meus Favoritos":
    fav_set = set(st.session_state["favoritos"])
    ativos_filtrados = [a for a in todos_ativos if a["ticker"] in fav_set]
elif filtro_setor == "💼 Apenas Minha Carteira":
    ativos_filtrados = [a for a in todos_ativos if a["ticker"] in posicoes_carteira]
elif filtro_setor != "Todos os Ativos da B3":
    sid = setores_dict.get(filtro_setor)
    if sid:
        with st.spinner(f"Filtrando setor {filtro_setor}..."):
            mapa_setores_ativos = carregar_tickers_por_setor((sid,))
        ativos_filtrados = [a for a in todos_ativos if a["ticker"] in mapa_setores_ativos]

if busca_tickers.strip():
    lista_busca = {x.strip().upper().replace(".SA", "") for x in busca_tickers.split(",") if x.strip()}
    ativos_filtrados = [a for a in ativos_filtrados if a["ticker"] in lista_busca]
elif filtro_setor not in ("💼 Apenas Minha Carteira", "⭐ Apenas Meus Favoritos"):
    ativos_filtrados = [a for a in ativos_filtrados if a["liq_2m"] >= liq_min]

preliminares = []
for a in ativos_filtrados:
    pt_bazin = a["dpa_12m"] / 0.06 if a["dpa_12m"] > 0 else None
    graham = math.sqrt(22.5 * a["lpa"] * a["vpa"]) if (a["lpa"] and a["vpa"] and a["lpa"] > 0 and a["vpa"] > 0) else None
    score_pre, _, _ = calcular_score(a, None, None, pt_bazin, graham)
    preliminares.append((score_pre, a))
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

with st.spinner(f"Buscando dados de 6 anos e nomes na B3 para {len(tickers_para_yf)} ativos..."):
    dados_yf = buscar_yahoo_lote(tuple(tickers_para_yf))


def montar_item_completo(a: dict) -> dict:
    t = a["ticker"]
    yf_info = dados_yf.get(t, {})
    cot = a.get("cotacao") or yf_info.get("cotacao_yf") or 0.0
    nome = yf_info.get("nome") or mapa_setores_ativos.get(t) or t
    lpa = yf_info.get("lpa_yf") if yf_info.get("lpa_yf") is not None else a.get("lpa")
    vpa = yf_info.get("vpa_yf") if yf_info.get("vpa_yf") is not None else a.get("vpa")
    roe = a.get("roe") if a.get("roe") is not None else yf_info.get("roe_yf")

    dpa_12m = yf_info.get("dpa_12m_yf") if yf_info.get("dpa_12m_yf") is not None else (a.get("dpa_12m") or 0.0)
    dy_12m = (dpa_12m / cot) * 100 if (dpa_12m and cot > 0) else (a.get("dy_12m") or 0.0)
    dpa_med_6a = yf_info.get("dpa_med_6a")
    anos_hist = yf_info.get("anos_hist", 0)
    dpa_proj = yf_info.get("dpa_proj")

    pt_med = (dpa_med_6a / 0.06) if (dpa_med_6a and dpa_med_6a > 0) else None
    pt_proj = (dpa_proj / 0.06) if (dpa_proj and dpa_proj > 0) else None
    pt_bazin = (dpa_12m / 0.06) if (dpa_12m and dpa_12m > 0) else None
    graham = math.sqrt(22.5 * lpa * vpa) if (lpa and vpa and lpa > 0 and vpa > 0) else None

    item = {
        **a,
        "cotacao": cot, "nome": nome, "setor_nome": mapa_setores_ativos.get(t, ""),
        "lpa": lpa, "vpa": vpa, "roe": roe,
        "dpa_12m": dpa_12m, "dy_12m": dy_12m,
        "dpa_med_6a": dpa_med_6a, "anos_hist": anos_hist, "dpa_proj": dpa_proj,
        "pt_med": pt_med, "pt_proj": pt_proj, "pt_bazin": pt_bazin, "graham": graham,
    }
    score, avg_ms, motivos = calcular_score(item, pt_med, pt_proj, pt_bazin, graham)
    item["score"] = score
    item["avg_ms"] = avg_ms
    item["motivos"] = motivos
    return item


resultados = [montar_item_completo(a) for _, a in preliminares]
resultados.sort(key=lambda x: x["score"], reverse=True)
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
        with st.expander(f"📋 Tabela Comparativa ({len(resultados)} ativos no filtro) — clique para minimizar/maximizar | clique em um Ticker para abrir o Raio-X", expanded=True):
            c_busca, c_ord1, c_ord2, c_ord3 = st.columns([1.8, 1.8, 1.4, 1.2])
            opcoes_ordenacao = {
                "Atratividade (Score)": "score",
                "Margem de Segurança Média (%)": "avg_ms",
                "Cotação (R$)": "cotacao",
                "Dividend Yield 12m (%)": "dy_12m",
                "P/L": "pl",
                "P/VP": "pvp",
                "ROE (%)": "roe",
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

            lista_tab = resultados
            if busca_tabela and busca_tabela.strip():
                termo = busca_tabela.strip().upper()
                lista_tab = [r for r in resultados if termo in r["ticker"] or termo in r["nome"].upper()]

            chave_ord = opcoes_ordenacao[col_escolhida]
            reverso = direcao.startswith("Decrescente")
            resultados_ordenados = sort_resultados(lista_tab, chave_ord, reverso)
            exibir = resultados_ordenados if max_linhas == 0 else resultados_ordenados[:int(max_linhas)]

            st.caption(f"Mostrando **{len(exibir)}** de **{len(lista_tab)}** ativos.")

            if not exibir:
                st.warning("Nenhum ativo corresponde à busca digitada na tabela.")
            else:
                linhas_html = []
                base_params = {"setor": filtro_setor, "liq": liq_label}
                if busca_tickers.strip():
                    base_params["busca"] = busca_tickers.strip()

                fav_set = set(st.session_state["favoritos"])
                for r in exibir:
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
                    setor_badge = f"<br><small style='opacity:0.65;'>{html.escape(r['setor_nome'])}</small>" if r["setor_nome"] else ""
                    estrela = " ⭐" if r["ticker"] in fav_set else ""

                    params_link = {**base_params, "ativo": r["ticker"]}
                    href = f"?{urlencode(params_link)}#raiox"

                    linha = (
                        "<tr>"
                        f"<td style='text-align:center; font-weight:700;'>{r['pos_ranking']}º<br><small style='opacity:0.75;'>{r['score']}</small></td>"
                        f"<td><a href='{href}' target='_self' style='color:#60a5fa; text-decoration:none; font-weight:700;'>🔎 {r['ticker']}</a>{estrela}<br><small style='opacity:0.8;'>{nome_esc}</small>{setor_badge}</td>"
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

                css_tabela = (
                    "<style>"
                    ".val-table-wrap{width:100%;overflow-x:auto;}"
                    ".val-table{width:100%;border-collapse:collapse;font-size:13px;line-height:1.4;}"
                    ".val-table th{background-color:rgba(128,128,128,0.18);text-align:left;padding:8px 6px;border-bottom:2px solid rgba(128,128,128,0.35);font-weight:600;font-size:12px;}"
                    ".val-table td{padding:8px 6px;border-bottom:1px solid rgba(128,128,128,0.22);vertical-align:middle;}"
                    ".val-table tr:hover td{background-color:rgba(128,128,128,0.08);}"
                    "</style>"
                )
                tabela_html = (
                    f"{css_tabela}"
                    "<div class='val-table-wrap'><table class='val-table'><thead><tr>"
                    "<th style='text-align:center;'>Rank<br><small>Score</small></th>"
                    "<th>Ticker / Empresa</th>"
                    f"<th>Cotação ({datetime.now(BRT).strftime('%d/%m/%Y %H:%M')}) & DY</th>"
                    "<th>Indicadores<br><small>(P/L | P/VP | ROE)</small></th>"
                    "<th>Dados Base<br><small>(LPA | VPA | DPAs)</small></th>"
                    "<th>Preço Teto Médio (6a) & MS</th>"
                    "<th>Preço Teto Projetivo & MS</th>"
                    "<th>Preço-Teto Bazin (12m) & MS</th>"
                    "<th>Preço Justo Graham & MS</th>"
                    f"</tr></thead><tbody>{''.join(linhas_html)}</tbody></table></div>"
                )
                st.markdown(tabela_html, unsafe_allow_html=True)
                st.caption(
                    "**Legenda siglas B3:** `ON` = Ordinária (voto) · `PN` = Preferencial (dividendos) · `UNT` = Unit (ON+PN) · "
                    "`ED/EJ` = Ex-Dividendo/JCP · `N1/N2/NM` = Nível 1, Nível 2 e Novo Mercado (governança).  \n"
                    "(*) Ativos com asterisco possuem menos de 6 anos completos de proventos no Yahoo Finance."
                )

        # --- RAIO-X DO ATIVO (EXPANDER MINIMIZÁVEL) ---
        st.markdown("<div id='raiox'></div>", unsafe_allow_html=True)
        opcoes_raiox = [r["ticker"] for r in (exibir if exibir else resultados)]
        idx_raiox = opcoes_raiox.index(ativo_url) if ativo_url in opcoes_raiox else 0
        with st.expander("🔎 Raio-X do Ativo (ou clique diretamente no código azul da tabela acima) — clique para minimizar/maximizar", expanded=True):
            ativo_escolhido = st.selectbox(
                "Ativo selecionado:",
                options=opcoes_raiox,
                index=idx_raiox,
            )
            item_raiox = next(r for r in resultados if r["ticker"] == ativo_escolhido)
            render_grafico_e_tabela_ativo(ativo_escolhido, item_raiox["nome"], base_ativo=item_raiox, key_prefix="tab1")

        # --- RANKING DE ATRATIVIDADE (EXPANDER + QUANTIDADE ESCOLHÍVEL) ---
        lista_rank_base = lista_tab if (busca_tabela and busca_tabela.strip() and lista_tab) else resultados
        total_rank = len(lista_rank_base)
        with st.expander(f"🏆 Ranking de Atratividade (Filtro Atual — até {total_rank} ativos) — clique para minimizar/maximizar", expanded=True):
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
                justificativa = "; ".join(r["motivos"]).capitalize() + "." if r["motivos"] else "Sem dados suficientes."
                estrela = " ⭐" if r["ticker"] in st.session_state["favoritos"] else ""
                blocos_ranking.append(
                    f"**{r['pos_ranking']}º Lugar: {r['ticker']}{estrela}** ({r['nome']}) | "
                    f"**Cotação: R$ {fmt_num(r['cotacao'])}** | "
                    f"**Score: {r['score']}/100**  \n"
                    f"_{justificativa}_"
                )
            st.markdown("\n\n".join(blocos_ranking))

        # --- SETOR DE ÚLTIMAS NOTÍCIAS E FATOS RELEVANTES (ABAIXO DO RANKING) ---
        ativos_para_news = exibir if exibir else lista_rank_base
        with st.expander("📰 Últimas Informações e Notícias dos Ativos Pesquisados / Filtrados — clique para minimizar/maximizar", expanded=True):
            if len(ativos_para_news) > 5:
                c_nw1, c_nw2 = st.columns([1.4, 2.6])
                with c_nw1:
                    qtd_news = st.number_input(
                        f"Buscar notícias para os primeiros N ativos (1 a {min(15, len(ativos_para_news))}):",
                        min_value=1,
                        max_value=min(15, len(ativos_para_news)),
                        value=5,
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
    default_comp = [r["ticker"] for r in resultados[:min(3, len(resultados))]] if resultados else tickers_b3[:3]
    selecionados = st.multiselect(
        "Escolha 2 ou mais ativos para comparar:",
        options=tickers_b3,
        default=default_comp,
    )

    if len(selecionados) < 2:
        st.info("Selecione pelo menos 2 ativos acima para visualizar a comparação.")
    else:
        mapa_todos = {a["ticker"]: a for a in todos_ativos}
        mapa_res = {r["ticker"]: r for r in resultados}
        faltantes = tuple(t for t in selecionados if t not in dados_yf)
        extra_yf = buscar_yahoo_lote(faltantes) if faltantes else {}

        itens_comp = []
        for t in selecionados:
            if t in mapa_res and t not in extra_yf:
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
            base_params_c = {"setor": filtro_setor, "liq": liq_label}
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
