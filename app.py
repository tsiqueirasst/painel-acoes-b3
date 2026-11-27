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

def formatar_nome_empresa_completo(nome_bruto: str) -> str:
    txt = " ".join((nome_bruto or "").split())
    if not txt:
        return ""
    txt = re.sub(r"\((Brasil|Brazil)\)", "", txt, flags=re.IGNORECASE)
    txt = re.sub(r"(?<!\w)(S\.A\.?|S/A|SA|Ltda\.?|S\.A)(?!\w)", "", txt, flags=re.IGNORECASE)
    txt = re.sub(r"\s*[-–/.,]+\s*$", "", " ".join(txt.split())).strip()
    if not txt:
        return ""
    minusculas = {"de", "da", "do", "das", "dos", "e", "em", "na", "no", "para", "com"}
    siglas = {
        "ISA", "B3", "MG", "SP", "RJ", "PR", "RS", "BA", "CE", "SC", "GO", "ES", "BR",
        "CPFL", "AES", "EDP", "CCR", "WEG", "BRF", "JBS", "MRV", "CSN", "TIM", "OI",
        "IRB", "XP", "BTG", "CEMIG", "COPEL", "TAESA", "SANEPAR", "COPASA", "SABESP",
        "PETROBRAS", "ELETROBRAS", "ENGIE", "KLABIN", "SUZANO", "VALE", "ITAU", "ITAÚ",
        "II", "III", "IV",
    }
    palavras = txt.split()
    out = []
    for idx, p in enumerate(palavras):
        p_clean = re.sub(r"^[^A-Za-zÀ-ÿ0-9]+|[^A-Za-zÀ-ÿ0-9]+$", "", p).upper()
        if p_clean in siglas:
            out.append(p.upper())
        elif idx > 0 and p.lower() in minusculas:
            out.append(p.lower())
        else:
            out.append(p[:1].upper() + p[1:].lower())
    return " ".join(out)

def limpar_nome_empresa(short_name: str, long_name: str, ticker: str) -> str:
    ln = " ".join((long_name or "").split())
    sn = " ".join((short_name or "").split())
    ln_low = ln.lower()

    if ln and (ln_low.startswith("banco ") or "banco " in ln_low or "unibanco" in ln_low or ln_low.startswith("caixa ")):
        limpo = re.sub(r"(?<!\w)Holding(?!\w)", "", ln, flags=re.IGNORECASE)
        res_b = formatar_nome_empresa_completo(limpo)
        if res_b:
            return res_b

    if ln:
        res_l = formatar_nome_empresa_completo(ln)
        if res_l and res_l.upper() != ticker.upper():
            return res_l

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
        res = formatar_nome_empresa_completo(" ".join(partes).strip())
        if res:
            return res

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
    t_work = f" {' '.join(re.sub(r'[^a-z0-9%]+', ' ', t).split())} "

    critico_kw = (
        "recuperacao judicial", "pedido de falencia", "falencia", "fraude",
        "calote", "default", "cvm investiga", "investigada pela cvm",
        "investigacao da cvm", "pf investiga", "mpf investiga",
        "rombo", "intervencao", "liquidacao extrajudicial",
    )
    if any(k in t_work for k in critico_kw):
        return "🚨 Risco Crítico", "critico", -5.0

    pts_pos = 0.0
    pts_neg = 0.0

    # 1) Expressões compostas positivas (redução de algo ruim / reversão de prejuízo)
    compostos_pos = (
        ("reverte prejuizo", 3.0),
        ("revertendo prejuizo", 3.0),
        ("sai de prejuizo", 3.0),
        ("sai do prejuizo", 3.0),
        ("saindo de prejuizo", 3.0),
        ("saindo do prejuizo", 3.0),
        ("reduz prejuizo", 2.5),
        ("reduziu prejuizo", 2.5),
        ("diminui prejuizo", 2.5),
        ("menor prejuizo", 2.5),
        ("prejuizo cai", 2.5),
        ("prejuizo recua", 2.5),
        ("sem prejuizo", 2.0),
        ("queda de despesas", 2.5),
        ("queda nas despesas", 2.5),
        ("queda das despesas", 2.5),
        ("queda de custos", 2.5),
        ("queda nos custos", 2.5),
        ("queda dos custos", 2.5),
        ("reducao de custos", 2.5),
        ("reducao nos custos", 2.5),
        ("reducao de despesas", 2.5),
        ("reducao nas despesas", 2.5),
        ("queda da divida", 2.5),
        ("queda na divida", 2.5),
        ("queda de divida", 2.5),
        ("reducao da divida", 2.5),
        ("reducao de divida", 2.5),
        ("queda de alavancagem", 2.5),
        ("queda na alavancagem", 2.5),
        ("queda da alavancagem", 2.5),
        ("reducao de alavancagem", 2.5),
        ("queda da inadimplencia", 2.5),
        ("queda na inadimplencia", 2.5),
        ("queda de inadimplencia", 2.5),
        ("reducao da inadimplencia", 2.5),
    )
    for frase, peso in compostos_pos:
        if frase in t_work:
            pts_pos += peso
            t_work = t_work.replace(frase, " ")

    # Padrões flexíveis positivos (ex: "queda nas despesas operacionais", "redução dos custos fixos")
    pat_pos_flex = re.compile(
        r"\b(?:queda|reducao|diminuicao|corte)\s+(?:de|da|das|do|dos|na|nas|no|nos)\s+"
        r"(?:despesas|custos|divida|alavancagem|inadimplencia)\b"
    )
    if pat_pos_flex.search(t_work):
        pts_pos += 2.5
        t_work = pat_pos_flex.sub(" ", t_work)

    # 2) Expressões compostas negativas (aumento de algo ruim / queda de lucro, receita, margem, dividendos)
    compostos_neg = (
        ("reverte lucro", 3.5),
        ("lucro desaba", 3.5),
        ("lucro despenca", 3.5),
        ("lucro cai", 3.0),
        ("lucro recua", 2.5),
        ("queda no lucro", 3.0),
        ("queda do lucro", 3.0),
        ("recuo no lucro", 2.5),
        ("corta dividendo", 3.0),
        ("suspende dividendo", 3.0),
        ("prejuizo dispara", 3.5),
        ("prejuizo sobe", 3.0),
        ("prejuizo aumenta", 3.0),
        ("prejuizo cresce", 3.0),
        ("divida dispara", 3.0),
        ("divida sobe", 2.5),
        ("divida cresce", 2.5),
        ("divida aumenta", 2.5),
        ("inadimplencia dispara", 3.0),
        ("inadimplencia sobe", 2.5),
        ("inadimplencia cresce", 2.5),
        ("despesas sobem", 2.5),
        ("custos sobem", 2.5),
        ("receita cai", 2.5),
        ("queda de receita", 2.5),
        ("queda na receita", 2.5),
        ("margem cai", 2.5),
        ("margem recua", 2.5),
    )
    for frase, peso in compostos_neg:
        if frase in t_work:
            pts_neg += peso
            t_work = t_work.replace(frase, " ")

    pat_lucro_neg = re.compile(r"\blucro(?:\s+\w+){0,2}\s+(?:cai|recua|desaba|despenca)\b")
    if pat_lucro_neg.search(t_work):
        pts_neg += 3.0
        t_work = pat_lucro_neg.sub(" ", t_work)

    # 3) Fatores positivos individuais sobre o texto restante
    pos_simples = (
        ("lucro recorde", 3.5),
        ("resultado recorde", 3.5),
        ("supera estimativas", 3.0),
        ("acima do esperado", 3.0),
        ("bate estimativas", 3.0),
        ("lucro dispara", 3.5),
        ("lucro salta", 3.5),
        ("lucro sobe", 3.0),
        ("lucro cresce", 3.0),
        ("lucro avanca", 3.0),
        ("melhora do resultado", 2.5),
        ("juros sobre capital", 2.5),
        ("dividendo", 2.5),
        ("provento", 2.5),
        (" jcp ", 2.5),
        ("recorde", 2.0),
        ("lucro", 2.0),
        ("dispara", 2.0),
        ("melhora", 1.5),
        ("supera", 1.5),
        ("aprova", 1.5),
        (" sobe ", 1.5),
        (" alta ", 1.5),
    )
    for kw, peso in pos_simples:
        if kw in t_work:
            pts_pos += peso
            t_work = t_work.replace(kw, " ")

    # 4) Fatores negativos individuais sobre o texto restante
    neg_simples = (
        ("abaixo do esperado", 2.5),
        ("abaixo das estimativas", 2.5),
        ("queda forte", 2.5),
        ("prejuizo", 2.5),
        ("decepciona", 2.5),
        ("frustra", 2.5),
        ("desaba", 2.5),
        ("derrete", 2.5),
        (" despenc", 2.5),
        ("tombo", 2.5),
        ("crise", 2.0),
        ("multa", 2.0),
        (" inadimpl", 2.0),
        (" rebaix", 2.0),
        (" queda ", 1.5),
        (" cai ", 1.5),
    )
    for kw, peso in neg_simples:
        if kw in t_work:
            pts_neg += peso
            t_work = t_work.replace(kw, " ")

    saldo_manchete = round(pts_pos - pts_neg, 2)
    if saldo_manchete > 0.0:
        pts_final = round(min(4.0, max(1.5, saldo_manchete)), 1)
        return "🟢 Positivo/Provento", "positivo", pts_final
    if saldo_manchete < 0.0:
        pts_final = round(max(-4.0, min(-1.5, saldo_manchete)), 1)
        return "🔴 Atenção", "negativo", pts_final

    corp_kw = (
        "privatiz", "leilao", "fusao", "aquisicao", " compra ", " venda ",
        "fato relevante", "estatiz", "governo", "desestatiz", "recompra", "bonificacao",
    )
    if any(k in t_work for k in corp_kw):
        return "🏛️ Fato/Corporativo", "corporativo", 0.0

    return "📰 Notícia", "neutro", 0.0


def _classificar_noticia(titulo: str) -> str:
    return _classificar_sentimento_noticia(titulo)[0]


def analisar_sentimento_noticias(itens: list[dict], agora_ts: float | None = None) -> dict:
    if not itens:
        return {
            "news_score": 0.0,
            "news_resumo": "⚪ Neutro",
            "qtd_30d": 0,
            "qtd_7d": 0,
            "tem_rj": False,
            "top_noticia_neg": None,
            "top_noticia_pos": None,
        }

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

    top_neg = None
    best_neg_key = (-1.0, 0.0)
    top_pos = None
    best_pos_key = (-1.0, 0.0)

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
        _, cat, saldo_manchete = _classificar_sentimento_noticia(titulo)
        pts = float(saldo_manchete)

        impacto = abs(pts) * peso_tempo
        soma_pts += pts * peso_tempo
        if "recuperacao judicial" in t_norm or "pedido de falencia" in t_norm or "falencia" in t_norm:
            tem_rj = True
        if cat in ("critico", "negativo") and saldo_manchete < 0.0:
            cand_n = (impacto, ts)
            if cand_n > best_neg_key:
                best_neg_key = cand_n
                top_neg = {
                    "titulo": titulo,
                    "fonte": it.get("fonte", ""),
                    "data_str": it.get("data_str", ""),
                    "link": it.get("link", ""),
                }
        if cat == "critico":
            cnt_critico += 1
        elif cat == "negativo" and saldo_manchete < 0.0:
            cnt_neg += 1
            if any(k in t_norm for k in ("prejuizo", "reverte lucro", "frustra", "queda de receita", "queda na receita")):
                tem_prej_ou_frustra = True
        elif cat == "positivo" and saldo_manchete > 0.0:
            cnt_pos += 1
            cand_p = (impacto, ts)
            if cand_p > best_pos_key:
                best_pos_key = cand_p
                top_pos = {
                    "titulo": titulo,
                    "fonte": it.get("fonte", ""),
                    "data_str": it.get("data_str", ""),
                    "link": it.get("link", ""),
                }
            if any(k in t_norm for k in ("dividendo", "jcp", "juros sobre capital", "provento")):
                tem_provento = True
            if any(k in t_norm for k in ("lucro", "resultado", "supera", "recorde", "reverte prejuizo")):
                tem_balanco_pos = True

    news_score = round(max(-10.0, min(10.0, soma_pts)), 1)

    if tem_rj:
        news_resumo = "🚨 Risco Crítico / RJ"
    elif cnt_critico > 0:
        news_resumo = "🔴 Alerta em Notícias"
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
        "tem_rj": tem_rj,
        "top_noticia_neg": top_neg,
        "top_noticia_pos": top_pos,
    }


@st.cache_data(ttl=1800, show_spinner=False)
def buscar_noticias_lote(tickers_tuple: tuple[str, ...], _v: int = 2) -> dict[str, list[dict]]:
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
                            "saldo_manchete": pts_s,
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


def _parse_i10_num(val: str | None) -> float | None:
    if val is None:
        return None
    s = str(val).strip()
    if not s or s in ("-", "--", "N/A", "N/D", "n/a", "n/d", "—"):
        return None
    s_clean = s.replace("R$", "").replace("%", "").strip()
    m = re.search(r"[-+]?\d{1,3}(?:\.\d{3})*(?:,\d+)?|[-+]?\d+(?:,\d+)?", s_clean)
    if not m:
        return None
    return parse_br_num(m.group(0))


def _fetch_investidor10(ticker: str) -> tuple[str, dict]:
    try:
        url = f"https://investidor10.com.br/acoes/{ticker.lower()}/"
        i10_headers = {
            **HEADERS,
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
            "Accept-Language": "pt-BR,pt;q=0.9,en-US;q=0.8,en;q=0.7",
            "Referer": "https://investidor10.com.br/",
        }
        resp = requests.get(url, headers=i10_headers, timeout=10)
        if resp.status_code != 200 or f"/{ticker.lower()}" not in resp.url.lower():
            return ticker, {}
        if "cf-browser-verification" in resp.text or "Just a moment" in resp.text[:1500]:
            return ticker, {}

        soup = BeautifulSoup(resp.text, "lxml")
        dados: dict[str, float] = {}

        for card in soup.find_all("div", class_=re.compile(r"\b_card\b")):
            hdr = card.find("div", class_=re.compile(r"_card-header"))
            body = card.find("div", class_=re.compile(r"_card-body"))
            if not hdr or not body:
                continue
            lbl = _norm_txt(" ".join(hdr.get_text(" ", strip=True).split()).rstrip("?").strip())
            if lbl == "cotacao":
                sp_cot = body.find("span", class_=re.compile(r"\bvalue\b")) or body.find("span")
                txt_cot = sp_cot.get_text(" ", strip=True) if sp_cot else ""
                if not txt_cot or "R$" not in txt_cot:
                    m_rs = re.search(r"R\$\s*[-+]?[\d.,]+", body.get_text(" ", strip=True))
                    txt_cot = m_rs.group(0) if m_rs else txt_cot
                val_c = _parse_i10_num(txt_cot)
                if val_c is not None and val_c > 0:
                    dados["cotacao_i10"] = val_c
            elif lbl in ("p/l", "p/vp", "dy", "dividend yield"):
                sp_v = body.find("span")
                val_v = _parse_i10_num(sp_v.get_text(" ", strip=True) if sp_v else body.get_text(" ", strip=True))
                if val_v is not None:
                    if lbl == "p/l":
                        dados["pl_i10"] = val_v
                    elif lbl == "p/vp":
                        dados["pvp_i10"] = val_v
                    else:
                        dados["dy_i10"] = val_v

        mapa_campos = {
            "p/l": "pl_i10",
            "p/vp": "pvp_i10",
            "lpa": "lpa_i10",
            "vpa": "vpa_i10",
            "roe": "roe_i10",
            "roic": "roic_i10",
            "dy": "dy_i10",
            "dividend yield": "dy_i10",
            "dividend yield (dy)": "dy_i10",
            "margem liquida": "marg_liq_i10",
            "margem ebit": "marg_ebit_i10",
            "ev/ebitda": "ev_ebitda_i10",
            "ev/ebit": "ev_ebit_i10",
            "liquidez corrente": "liq_corr_i10",
            "divida bruta / patrimonio": "div_brut_patrim_i10",
            "div. bruta / patrimonio": "div_brut_patrim_i10",
            "cagr receitas 5 anos": "cresc_rec_5a_i10",
            "cagr receita 5 anos": "cresc_rec_5a_i10",
        }

        container_ind = soup.find(id="table-indicators") or soup
        for cell in container_ind.find_all("div", class_=re.compile(r"\bcell\b")):
            val_div = cell.find("div", class_=re.compile(r"\bvalue\b"))
            lbl_raw = ""
            for child in cell.find_all(["span", "h3", "h4", "div"], recursive=False):
                cls_ch = " ".join(child.get("class", []))
                if "value" in cls_ch or "compare" in cls_ch:
                    continue
                t_ch = " ".join(child.get_text(" ", strip=True).split()).rstrip("?").strip()
                if t_ch:
                    lbl_raw = t_ch
                    break
            if not lbl_raw:
                sp_first = cell.find("span")
                if sp_first and (not val_div or sp_first not in val_div.descendants):
                    lbl_raw = " ".join(sp_first.get_text(" ", strip=True).split()).rstrip("?").strip()

            lbl_norm = _norm_txt(lbl_raw)
            chave_dst = mapa_campos.get(lbl_norm)
            if not chave_dst:
                continue

            txt_val = ""
            if val_div:
                for sp in val_div.find_all("span"):
                    cand_s = " ".join(sp.get_text(" ", strip=True).split())
                    if re.search(r"[\d]|^-+$|^N/[AD]$", cand_s, re.IGNORECASE):
                        txt_val = cand_s
                        break
                if not txt_val:
                    txt_val = re.split(r"\bSetor\b|\bSubsetor\b|\bSegmento\b", val_div.get_text(" ", strip=True), flags=re.IGNORECASE)[0]
            else:
                txt_cell = " ".join(cell.get_text(" ", strip=True).split())
                txt_sem_lbl = txt_cell[len(lbl_raw):].strip() if txt_cell.lower().startswith(lbl_raw.lower()) else txt_cell
                txt_val = re.split(r"\bSetor\b|\bSubsetor\b|\bSegmento\b", txt_sem_lbl, flags=re.IGNORECASE)[0]

            val_num = _parse_i10_num(txt_val)
            if val_num is not None:
                dados[chave_dst] = val_num

        return ticker, dados
    except Exception:
        return ticker, {}


@st.cache_data(ttl=900, show_spinner=False)
def buscar_investidor10_lote(tickers_tuple: tuple[str, ...]) -> dict[str, dict]:
    if not tickers_tuple:
        return {}
    out: dict[str, dict] = {}
    with ThreadPoolExecutor(max_workers=6) as ex:
        for tk, dados in ex.map(_fetch_investidor10, tickers_tuple):
            out[tk] = dados
    return out


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

@st.cache_data(ttl=86400, show_spinner=False)
def carregar_nomes_cvm_tickers() -> dict[str, str]:
    """Retorna mapa {ticker: Nome Completo Formatado} direto da base cadastral da CVM."""
    mapa_tk, _ = carregar_mapa_cvm_tickers()
    if not mapa_tk:
        return {}
    mapa_cnpj_nome: dict[str, str] = {}
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
                usecols=lambda c: c in {"CNPJ_CIA", "DENOM_SOCIAL", "DENOM_COMERC"},
            )
            for _, row in df_cad.iterrows():
                cnpj_c = str(row.get("CNPJ_CIA") or "").strip()
                if not cnpj_c:
                    continue
                soc = formatar_nome_empresa_completo(str(row.get("DENOM_SOCIAL") or ""))
                com = formatar_nome_empresa_completo(str(row.get("DENOM_COMERC") or ""))
                if soc and com:
                    soc_n = _norm_txt(soc)
                    com_n = _norm_txt(com)
                    if com_n in soc_n or len(com) <= 3:
                        nome_f = soc
                    elif soc_n in com_n:
                        nome_f = com
                    else:
                        nome_f = f"{soc} ({com})" if len(soc) <= 38 else com
                else:
                    nome_f = soc or com
                if nome_f:
                    mapa_cnpj_nome[cnpj_c] = nome_f
    except Exception:
        return {}

    return {tk: mapa_cnpj_nome[cnpj] for tk, cnpj in mapa_tk.items() if cnpj in mapa_cnpj_nome}


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
        anos_divs_consec = 0
        meses_dividendos: list[int] = []

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

            divs_pos = divs[divs > 0]
            if not divs_pos.empty:
                divs_4a = divs_pos[divs_pos.index >= (hoje - timedelta(days=365 * 4))]
                if not divs_4a.empty:
                    meses_dividendos = sorted({int(m) for m in divs_4a.index.month})
                anos_com_div = {int(y) for y in divs_pos.index.year}
                yr_chk = ano_atual if ano_atual in anos_com_div else (ano_atual - 1)
                while yr_chk in anos_com_div:
                    anos_divs_consec += 1
                    yr_chk -= 1

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
            "anos_divs_consec": anos_divs_consec,
            "meses_dividendos": meses_dividendos,
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


@st.cache_data(ttl=180, show_spinner=False)
def buscar_ohlcv_preco(
    ticker: str,
    periodo_label: str,
    ajustada: bool,
    cot_live: float | None = None,
) -> pd.DataFrame:
    tk = yf.Ticker(f"{ticker}.SA")
    eh_intraday = periodo_label in ("1 D", "7 D")

    if periodo_label == "1 D":
        df = tk.history(period="5d", interval="15m", auto_adjust=False)
        if df is not None and not df.empty:
            df.index = _idx_para_brt_naive(df.index)
            df = df[df.index.date == df.index.date[-1]]
    elif periodo_label == "7 D":
        df = tk.history(period="1mo", interval="1h", auto_adjust=False)
        if df is not None and not df.empty:
            df.index = _idx_para_brt_naive(df.index)
            df = df[df.index >= (df.index.max() - timedelta(days=7))]
    elif periodo_label == "15 A":
        df = tk.history(period="max", interval="1d", auto_adjust=ajustada)
        if df is not None and not df.empty:
            df.index = _idx_para_brt_naive(df.index)
            df = df[df.index >= (df.index.max() - pd.DateOffset(years=15))]
    else:
        mapa = {"30 D": "1mo", "6 M": "6mo", "YTD": "ytd", "1 A": "1y", "5 A": "5y", "10 A": "10y"}
        df = tk.history(period=mapa.get(periodo_label, "1y"), interval="1d", auto_adjust=ajustada)
        if df is not None and not df.empty:
            df.index = _idx_para_brt_naive(df.index)

    if df is None or df.empty or "Close" not in df.columns:
        return pd.DataFrame()

    cols_ok = [c for c in ("Open", "High", "Low", "Close", "Volume") if c in df.columns]
    df = df[cols_ok].dropna(subset=["Close"]).copy()
    if df.empty:
        return df

    # Sincroniza pregões recentes caso o endpoint diário (1d) do Yahoo esteja 1+ dia atrasado
    if not eh_intraday:
        try:
            df_5d = tk.history(period="5d", interval="15m", auto_adjust=False)
            if df_5d is not None and not df_5d.empty and "Close" in df_5d.columns:
                df_5d.index = _idx_para_brt_naive(df_5d.index)
                ult_data_df = df.index.normalize().max()
                dias_novos = sorted({d for d in df_5d.index.normalize() if d > ult_data_df})
                for d_n in dias_novos:
                    sub_d = df_5d[df_5d.index.normalize() == d_n].dropna(subset=["Close"])
                    if not sub_d.empty:
                        nova_linha = {
                            "Open": float(sub_d["Open"].iloc[0]) if "Open" in sub_d.columns else float(sub_d["Close"].iloc[0]),
                            "High": float(sub_d["High"].max()) if "High" in sub_d.columns else float(sub_d["Close"].max()),
                            "Low": float(sub_d["Low"].min()) if "Low" in sub_d.columns else float(sub_d["Close"].min()),
                            "Close": float(sub_d["Close"].iloc[-1]),
                            "Volume": float(sub_d["Volume"].sum()) if "Volume" in sub_d.columns else 0.0,
                        }
                        df.loc[d_n] = {k: nova_linha[k] for k in df.columns}
        except Exception:
            pass

        if cot_live and float(cot_live) > 0.0:
            cot_f = float(cot_live)
            ult_data_df = df.index.normalize().max()
            dt_fund_ts = None
            try:
                det_f = buscar_detalhes_fundamentus(ticker)
                dt_str_f = (det_f.get("Data últ cot") or "").strip()
                if dt_str_f:
                    dt_fund_ts = pd.to_datetime(dt_str_f, format="%d/%m/%Y", errors="coerce")
            except Exception:
                dt_fund_ts = None

            if dt_fund_ts is not None and pd.notna(dt_fund_ts) and dt_fund_ts > ult_data_df:
                nova_l = {"Open": cot_f, "High": cot_f, "Low": cot_f, "Close": cot_f, "Volume": 0.0}
                df.loc[dt_fund_ts] = {k: nova_l[k] for k in df.columns}
            elif abs(float(df["Close"].iloc[-1]) - cot_f) / cot_f > 0.001:
                idx_ult = df.index[-1]
                df.loc[idx_ult, "Close"] = cot_f
                if "High" in df.columns:
                    df.loc[idx_ult, "High"] = max(float(df.loc[idx_ult, "High"]), cot_f)
                if "Low" in df.columns:
                    df.loc[idx_ult, "Low"] = min(float(df.loc[idx_ult, "Low"]), cot_f)
    elif cot_live and float(cot_live) > 0.0 and periodo_label == "1 D":
        cot_f = float(cot_live)
        if abs(float(df["Close"].iloc[-1]) - cot_f) / cot_f > 0.002:
            df.loc[df.index[-1], "Close"] = cot_f

    return df.sort_index()

def buscar_historico_preco(
    ticker: str,
    periodo_label: str,
    ajustada: bool,
    cot_live: float | None = None,
) -> pd.Series:
    df = buscar_ohlcv_preco(ticker, periodo_label, ajustada, cot_live=cot_live)
    if df is None or df.empty or "Close" not in df.columns:
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


_TABELA_IOF_RF = (
    0, 96, 93, 90, 86, 83, 80, 76, 73, 70, 66, 63, 60, 56, 53,
    50, 46, 43, 40, 36, 33, 30, 26, 23, 20, 16, 13, 10, 6, 3,
)


def _calc_impostos_renda_fixa(ganho_bruto: float, dias_corridos: int) -> tuple[float, float, float, float, float]:
    """Retorna (iof_val, ir_val, aliq_iof_pct, aliq_ir_pct, imposto_total)."""
    if ganho_bruto <= 0.0:
        if dias_corridos <= 180:
            aliq_ir = 22.5
        elif dias_corridos <= 360:
            aliq_ir = 20.0
        elif dias_corridos <= 720:
            aliq_ir = 17.5
        else:
            aliq_ir = 15.0
        return 0.0, 0.0, 0.0, aliq_ir, 0.0

    aliq_iof_pct = float(_TABELA_IOF_RF[dias_corridos]) if 0 <= dias_corridos < 30 else 0.0
    iof_val = ganho_bruto * (aliq_iof_pct / 100.0)
    base_ir = max(0.0, ganho_bruto - iof_val)

    if dias_corridos <= 180:
        aliq_ir_pct = 22.5
    elif dias_corridos <= 360:
        aliq_ir_pct = 20.0
    elif dias_corridos <= 720:
        aliq_ir_pct = 17.5
    else:
        aliq_ir_pct = 15.0

    ir_val = base_ir * (aliq_ir_pct / 100.0)
    return iof_val, ir_val, aliq_iof_pct, aliq_ir_pct, (iof_val + ir_val)


@st.cache_data(ttl=43200, show_spinner=False)
def buscar_historico_selic_bcb() -> tuple[pd.Series, float | None]:
    """Retorna (serie_selic_diaria_pct, selic_anual_atual_pct) via API SGS do Banco Central."""
    hoje_brt = datetime.now(BRT).date()
    janelas = [
        (hoje_brt - timedelta(days=365 * 16 + 30), hoje_brt - timedelta(days=365 * 8 + 1)),
        (hoje_brt - timedelta(days=365 * 8), hoje_brt),
    ]

    def _baixar_serie_sgs(cod_serie: int) -> pd.Series:
        regs = []
        for d_ini, d_fim in janelas:
            try:
                url = (
                    f"https://api.bcb.gov.br/dados/serie/bcdata.sgs.{cod_serie}/dados"
                    f"?formato=json&dataInicial={d_ini.strftime('%d/%m/%Y')}&dataFinal={d_fim.strftime('%d/%m/%Y')}"
                )
                resp = requests.get(url, headers=HEADERS, timeout=12)
                if resp.status_code == 200:
                    js = resp.json()
                    if isinstance(js, list):
                        regs.extend(js)
            except Exception:
                continue
        if not regs:
            return pd.Series(dtype=float)
        df_s = pd.DataFrame(regs)
        if not {"data", "valor"}.issubset(df_s.columns):
            return pd.Series(dtype=float)
        df_s["dt"] = pd.to_datetime(df_s["data"], format="%d/%m/%Y", errors="coerce")
        df_s["val"] = pd.to_numeric(df_s["valor"], errors="coerce")
        df_s = df_s.dropna(subset=["dt", "val"]).drop_duplicates(subset=["dt"]).sort_values("dt")
        if df_s.empty:
            return pd.Series(dtype=float)
        return pd.Series(df_s["val"].values, index=pd.DatetimeIndex(df_s["dt"]))

    serie = _baixar_serie_sgs(11)
    if serie.empty:
        serie = _baixar_serie_sgs(12)

    selic_aa = None
    for cod_aa in (1178, 432):
        try:
            url_aa = (
                f"https://api.bcb.gov.br/dados/serie/bcdata.sgs.{cod_aa}/dados"
                f"?formato=json&dataInicial={(hoje_brt - timedelta(days=30)).strftime('%d/%m/%Y')}&dataFinal={hoje_brt.strftime('%d/%m/%Y')}"
            )
            resp_aa = requests.get(url_aa, headers=HEADERS, timeout=8)
            if resp_aa.status_code == 200:
                arr_aa = resp_aa.json()
                if isinstance(arr_aa, list) and arr_aa:
                    v_aa = float(arr_aa[-1]["valor"])
                    if v_aa > 0:
                        selic_aa = v_aa
                        break
        except Exception:
            continue

    if selic_aa is None and not serie.empty:
        r_ult = float(serie.iloc[-1]) / 100.0
        if r_ult > 0:
            selic_aa = ((1.0 + r_ult) ** 252.0 - 1.0) * 100.0

    return serie, selic_aa


@st.cache_data(ttl=43200, show_spinner=False)
def calcular_selic_calculadora_cidadao(dt_ini_str: str, dt_fim_str: str, valor: float) -> float | None:
    """Consulta exatamente a Calculadora do Cidadão do BCB (Correção pela Taxa Selic)."""
    try:
        url = "https://www3.bcb.gov.br/CALCIDADAO/publico/corrigirPelaSelic.do?method=corrigirPelaSelic"
        payload = {
            "aba": "4",
            "dataInicial": dt_ini_str,
            "dataFinal": dt_fim_str,
            "valorCorrecao": f"{valor:.2f}".replace(".", ","),
        }
        resp = requests.post(
            url,
            data=payload,
            headers={
                **HEADERS,
                "Referer": "https://www3.bcb.gov.br/CALCIDADAO/publico/exibirFormCorrecaoValores.do?method=exibirFormCorrecaoValores&aba=4",
            },
            timeout=6,
        )
        if resp.status_code != 200:
            return None
        soup = BeautifulSoup(resp.text, "lxml")
        txt = " ".join(soup.get_text(" ", strip=True).split())
        m = re.search(r"Valor corrigido na data final\s*:?\s*R\$\s*([\d.]+,\d{2})", txt, flags=re.IGNORECASE)
        if m:
            return parse_br_num(m.group(1))
        m_idx = re.search(r"[ÍI]ndice de corre[çc][ãa]o no per[íi]odo\s*:?\s*([\d.]+,\d+)", txt, flags=re.IGNORECASE)
        if m_idx:
            fator = parse_br_num(m_idx.group(1))
            if fator and fator > 0:
                return valor * fator
    except Exception:
        pass
    return None


def _calc_tesouro_selic_capital_mensal(meta_mensal: float, selic_aa_pct: float, aliq_ir: float) -> float:
    """Calcula capital necessário hoje no Tesouro Selic para gerar meta_mensal líquida (com IR e Custódia B3 0,20% a.a. > R$ 10k)."""
    if meta_mensal <= 0.0 or selic_aa_pct <= 0.0:
        return 0.0
    selic_am_bruto = ((1.0 + (selic_aa_pct / 100.0)) ** (1.0 / 12.0)) - 1.0
    taxa_liq_sem_b3 = selic_am_bruto * (1.0 - aliq_ir)
    if taxa_liq_sem_b3 <= 0.0:
        return 0.0
    cap_0 = meta_mensal / taxa_liq_sem_b3
    if cap_0 <= 10_000.0:
        return cap_0
    taxa_b3_am = ((1.0 + 0.002) ** (1.0 / 12.0)) - 1.0
    denom = taxa_liq_sem_b3 - taxa_b3_am
    if denom <= 0.0:
        return cap_0
    return (meta_mensal - (10_000.0 * taxa_b3_am)) / denom


def _idx_para_brt_naive(idx) -> pd.DatetimeIndex:
    dt_idx = pd.to_datetime(idx)
    if dt_idx.tz is not None:
        return dt_idx.tz_convert(BRT).tz_localize(None)
    return dt_idx


@st.cache_data(ttl=120, show_spinner=False)
def buscar_dados_ibov_google(periodo: str) -> dict:
    tk = yf.Ticker("^BVSP")
    prev_close = None
    abertura = None
    alta = None
    baixa = None
    alt_52s = None
    bai_52s = None
    serie = pd.Series(dtype=float)
    dt_ult = None

    try:
        try:
            fi = tk.fast_info
            if fi:
                prev_close = fi.get("previousClose") or fi.get("regularMarketPreviousClose")
                alt_52s = fi.get("yearHigh")
                bai_52s = fi.get("yearLow")
        except Exception:
            pass

        h1y = tk.history(period="1y", interval="1d", auto_adjust=False)
        if h1y is not None and not h1y.empty:
            h1y.index = _idx_para_brt_naive(h1y.index)
        h5d = tk.history(period="5d", interval="5m", auto_adjust=False)
        if h5d is not None and not h5d.empty:
            h5d.index = _idx_para_brt_naive(h5d.index)

        # Sincroniza resumo diário com o último pregão do intraday (caso o 1d esteja 1 dia atrás)
        if h5d is not None and not h5d.empty and "Close" in h5d.columns:
            c5 = h5d["Close"].dropna()
            if not c5.empty:
                ult_dia_intra = c5.index.normalize().max()
                sub_intra = h5d[h5d.index.normalize() == ult_dia_intra].dropna(subset=["Close"])
                if h1y is not None and not h1y.empty:
                    ult_dia_1y = h1y.index.normalize().max()
                    if ult_dia_intra > ult_dia_1y:
                        prev_close = float(h1y["Close"].dropna().iloc[-1])
                        abertura = float(sub_intra["Open"].iloc[0]) if "Open" in sub_intra.columns else float(sub_intra["Close"].iloc[0])
                        alta = float(sub_intra["High"].max()) if "High" in sub_intra.columns else float(sub_intra["Close"].max())
                        baixa = float(sub_intra["Low"].min()) if "Low" in sub_intra.columns else float(sub_intra["Close"].min())
                    else:
                        ult = h1y.iloc[-1]
                        abertura = float(ult["Open"]) if pd.notna(ult.get("Open")) else None
                        alta = float(ult["High"]) if pd.notna(ult.get("High")) else None
                        baixa = float(ult["Low"]) if pd.notna(ult.get("Low")) else None
                        if len(h1y) >= 2:
                            prev_close = float(h1y["Close"].dropna().iloc[-2])
        elif h1y is not None and not h1y.empty:
            ult = h1y.iloc[-1]
            abertura = float(ult["Open"]) if pd.notna(ult.get("Open")) else None
            alta = float(ult["High"]) if pd.notna(ult.get("High")) else None
            baixa = float(ult["Low"]) if pd.notna(ult.get("Low")) else None
            if len(h1y) >= 2 and not prev_close:
                prev_close = float(h1y["Close"].dropna().iloc[-2])

        if h1y is not None and not h1y.empty:
            if not alt_52s and "High" in h1y.columns:
                alt_52s = float(h1y["High"].dropna().max())
            if not bai_52s and "Low" in h1y.columns:
                bai_52s = float(h1y["Low"].dropna().min())
            if alta and alt_52s:
                alt_52s = max(float(alt_52s), alta)
            if baixa and bai_52s:
                bai_52s = min(float(bai_52s), baixa)

        if periodo == "1 D":
            if h5d is not None and not h5d.empty and "Close" in h5d.columns:
                c5 = h5d["Close"].dropna()
                if not c5.empty:
                    ult_d = c5.index.date[-1]
                    serie = c5[c5.index.date == ult_d]
                    ant = c5[c5.index.date < ult_d]
                    if not ant.empty and not prev_close:
                        prev_close = float(ant.iloc[-1])
            elif h1y is not None and not h1y.empty:
                serie = h1y["Close"].dropna().tail(1)
        elif periodo == "5 D":
            if h5d is not None and not h5d.empty and "Close" in h5d.columns:
                serie = h5d["Close"].dropna()
        else:
            mapa_per = {
                "1 M": ("1mo", "1d"),
                "6 M": ("6mo", "1d"),
                "YTD": ("ytd", "1d"),
                "1 A": ("1y", "1d"),
                "5 A": ("5y", "1wk"),
                "Máx": ("max", "1wk"),
            }
            per_yf, int_yf = mapa_per.get(periodo, ("1mo", "1d"))
            df_p = h1y if periodo == "1 A" else tk.history(period=per_yf, interval=int_yf, auto_adjust=False)
            if df_p is not None and not df_p.empty and "Close" in df_p.columns:
                if periodo != "1 A":
                    df_p.index = _idx_para_brt_naive(df_p.index)
                serie = df_p["Close"].dropna().copy()
                if h5d is not None and not h5d.empty and "Close" in h5d.columns and not serie.empty:
                    c5 = h5d["Close"].dropna()
                    ult_d_p = serie.index.normalize().max()
                    for d_n in sorted({d for d in c5.index.normalize() if d > ult_d_p}):
                        sub_d = c5[c5.index.normalize() == d_n]
                        if not sub_d.empty:
                            serie.loc[d_n] = float(sub_d.iloc[-1])
                    serie = serie.sort_index()

        if not serie.empty:
            dt_ult = serie.index[-1].to_pydatetime()
    except Exception:
        pass

    ref_px = float(prev_close) if (periodo == "1 D" and prev_close) else (float(serie.iloc[0]) if not serie.empty else None)
    return {
        "serie": serie,
        "ref_px": ref_px,
        "dt_ult": dt_ult,
        "prev_close": float(prev_close) if prev_close else None,
        "abertura": abertura,
        "alta": alta,
        "baixa": baixa,
        "alt_52s": float(alt_52s) if alt_52s else None,
        "bai_52s": float(bai_52s) if bai_52s else None,
    }

@st.fragment
def render_widget_ibov_google():
    meses_pt = {
        1: "jan.", 2: "fev.", 3: "mar.", 4: "abr.", 5: "mai.", 6: "jun.",
        7: "jul.", 8: "ago.", 9: "set.", 10: "out.", 11: "nov.", 12: "dez.",
    }
    periodos_g = ["1 D", "5 D", "1 M", "6 M", "YTD", "1 A", "5 A", "Máx"]

    with st.container(border=True):
        st.markdown(
            "<span class='ibov-google-anchor' style='display:none;'></span>"
            "<style>"
            "div[data-testid='stVerticalBlockBorderWrapper']:has(.ibov-google-anchor){"
            "padding:10px 14px!important;}"
            "</style>",
            unsafe_allow_html=True,
        )

        if hasattr(st, "segmented_control"):
            periodo_sel = st.session_state.get("ibov_google_per", "1 D") or "1 D"
        else:
            periodo_sel = st.session_state.get("ibov_google_per_rad", "1 D")

        dados_ib = buscar_dados_ibov_google(periodo_sel)
        serie = dados_ib["serie"]
        ref_px = dados_ib["ref_px"]
        dt_ult = dados_ib["dt_ult"]

        if serie.empty:
            st.markdown(
                "<div style='display:flex; align-items:center; gap:8px; margin-bottom:6px;'>"
                "<span style='display:inline-flex; align-items:center; justify-content:center; padding:0 7px; height:28px; "
                "border-radius:6px; background:#1a73e8; color:#fff; font-weight:800; font-size:11px;'>IBOV</span>"
                "<div><div style='font-size:14px; font-weight:700; line-height:1.1;'>Ibovespa</div>"
                "<div style='font-size:11px; opacity:0.7;'>INDEXBVMF: IBOV</div></div></div>",
                unsafe_allow_html=True,
            )
            st.caption("Cotação do Ibovespa temporariamente indisponível.")
            return

        p_fim = float(serie.iloc[-1])
        ref_val = float(ref_px) if (ref_px is not None and ref_px > 0) else float(serie.iloc[0])
        diff_val = p_fim - ref_val
        diff_pct = (diff_val / ref_val) * 100.0 if ref_val > 0 else 0.0

        if abs(diff_pct) < 0.005:
            cor_ln = "#9aa0a6"
            fill_ln = "rgba(154,160,166,0.15)"
            pill_bg = "rgba(154,160,166,0.22)"
            pill_fg = "#e5e7eb"
            seta_txt = ""
        elif diff_val > 0:
            cor_ln = "#22c55e"
            fill_ln = "rgba(34,197,94,0.18)"
            pill_bg = "rgba(34,197,94,0.20)"
            pill_fg = "#4ade80"
            seta_txt = "↑ "
        else:
            cor_ln = "#ef4444"
            fill_ln = "rgba(239,68,68,0.18)"
            pill_bg = "rgba(239,68,68,0.20)"
            pill_fg = "#f87171"
            seta_txt = "↓ "

        sinal_abs = "+" if diff_val > 0.004 else ""
        lbl_jan = "hoje" if periodo_sel == "1 D" else f"({periodo_sel})"
        if dt_ult is not None:
            dt_str = f"{dt_ult.day} de {meses_pt.get(dt_ult.month, '')}, {dt_ult.strftime('%H:%M')} BRT"
        else:
            dt_str = datetime.now(BRT).strftime("%d/%m/%Y %H:%M BRT")

        st.markdown(
            "<div style='display:flex; justify-content:space-between; align-items:flex-start; flex-wrap:wrap; gap:8px; margin-bottom:4px;'>"
            "<div style='display:flex; align-items:center; gap:9px;'>"
            "<span style='display:inline-flex; align-items:center; justify-content:center; padding:0 7px; height:30px; "
            "border-radius:7px; background:#1a73e8; color:#ffffff; font-weight:800; font-size:11px; flex-shrink:0;'>IBOV</span>"
            "<div>"
            "<div style='font-size:15px; font-weight:700; line-height:1.15;'>Ibovespa</div>"
            "<div style='font-size:11px; opacity:0.72;'>INDEXBVMF: IBOV</div>"
            "</div>"
            "</div>"
            "<div style='text-align:right;'>"
            "<div style='display:flex; align-items:baseline; justify-content:flex-end; gap:6px; flex-wrap:wrap;'>"
            f"<span style='font-size:21px; font-weight:700; line-height:1.1;'>{fmt_num(p_fim)}</span>"
            "<span style='font-size:11px; opacity:0.72;'>pts</span>"
            f"<span style='display:inline-block; padding:2px 7px; border-radius:6px; font-size:11px; font-weight:700; "
            f"background:{pill_bg}; color:{pill_fg};'>{seta_txt}{fmt_num(abs(diff_pct) if diff_pct < 0 else diff_pct)}%</span>"
            f"<span style='font-size:12px; font-weight:600; color:{pill_fg};'>{sinal_abs}{fmt_num(diff_val)} {lbl_jan}</span>"
            "</div>"
            f"<div style='font-size:10.5px; opacity:0.68; margin-top:2px;'>{html.escape(dt_str)}</div>"
            "</div>"
            "</div>",
            unsafe_allow_html=True,
        )

        if hasattr(st, "segmented_control"):
            periodo_sel_new = st.segmented_control(
                "Período IBOV:",
                options=periodos_g,
                default=periodo_sel,
                label_visibility="collapsed",
                key="ibov_google_per",
                width="stretch",
            )
            if not periodo_sel_new:
                periodo_sel_new = periodo_sel
        else:
            periodo_sel_new = st.radio(
                "Período IBOV:",
                options=periodos_g,
                index=periodos_g.index(periodo_sel) if periodo_sel in periodos_g else 0,
                horizontal=True,
                label_visibility="collapsed",
                key="ibov_google_per_rad",
            )

        if periodo_sel_new != periodo_sel:
            st.rerun()

        fig_ib = go.Figure()
        fmt_hv = "%{x|%d/%m %H:%M}" if periodo_sel in ("1 D", "5 D") else "%{x|%d/%m/%Y}"
        fig_ib.add_trace(
            go.Scatter(
                x=serie.index,
                y=serie.values,
                mode="lines",
                name="IBOV",
                line=dict(color=cor_ln, width=2.0),
                fill="tozeroy",
                fillcolor=fill_ln,
                hovertemplate=f"{fmt_hv}<br><b>%{{y:,.2f}} pts</b><extra></extra>",
            )
        )
        fig_ib.add_trace(
            go.Scatter(
                x=[serie.index[-1]],
                y=[p_fim],
                mode="markers",
                marker=dict(color=cor_ln, size=7),
                hoverinfo="skip",
            )
        )

        y_vals_all = list(serie.values) + [ref_val]
        y_min = min(y_vals_all)
        y_max = max(y_vals_all)
        pad_y = (y_max - y_min) * 0.14 if y_max > y_min else max(50.0, p_fim * 0.01)
        ref_lbl = f"Pré-fech.<br><b>{fmt_num(ref_val, 0)}</b>" if periodo_sel == "1 D" else f"Início<br><b>{fmt_num(ref_val, 0)}</b>"

        fig_ib.add_hline(
            y=ref_val,
            line_dash="dot",
            line_width=1.3,
            line_color="rgba(154,160,166,0.65)",
        )
        fig_ib.update_layout(
            height=185,
            margin=dict(l=4, r=72, t=28, b=24),
            paper_bgcolor="rgba(0,0,0,0)",
            plot_bgcolor="rgba(0,0,0,0)",
            showlegend=False,
            hovermode="x unified",
            dragmode="pan",
            xaxis=dict(
                showgrid=False,
                zeroline=False,
                tickfont=dict(size=10),
                tickformat="%H:%M" if periodo_sel == "1 D" else ("%d/%m" if periodo_sel in ("5 D", "1 M", "6 M", "YTD") else "%m/%Y"),
                nticks=5,
                showspikes=True,
                spikemode="across",
                spikesnap="cursor",
                spikethickness=1,
                spikecolor="rgba(148,163,184,0.55)",
                spikedash="dash",
            ),
            yaxis=dict(
                side="right",
                showgrid=True,
                gridcolor="rgba(128,128,128,0.20)",
                zeroline=False,
                tickfont=dict(size=10),
                range=[max(0.0, y_min - pad_y), y_max + pad_y],
                nticks=4,
                showspikes=True,
                spikemode="across",
                spikesnap="cursor",
                spikethickness=1,
                spikecolor="rgba(148,163,184,0.55)",
                spikedash="dash",
            ),
            annotations=[
                dict(
                    xref="paper",
                    x=0.01,
                    y=ref_val,
                    xanchor="left",
                    yanchor="bottom",
                    text=ref_lbl,
                    showarrow=False,
                    align="left",
                    font=dict(size=10, color="rgba(200,205,213,0.9)"),
                ),
                dict(
                    xref="paper",
                    x=1.01,
                    y=p_fim,
                    xanchor="left",
                    yanchor="middle",
                    text=f"<b>{fmt_num(p_fim, 0)}</b>",
                    showarrow=False,
                    font=dict(color="white", size=10.5),
                    bgcolor=cor_ln,
                    borderpad=3,
                ),
            ],
        )
        st.plotly_chart(
            fig_ib,
            use_container_width=True,
            config={"scrollZoom": True, "displaylogo": False, "modeBarButtonsToRemove": ["zoom2d", "zoomIn2d", "zoomOut2d", "lasso2d", "select2d"]},
            key="ibov_google_chart",
        )

        pf_s = fmt_num(dados_ib["prev_close"]) if dados_ib.get("prev_close") is not None else "—"
        ab_s = fmt_num(dados_ib["abertura"]) if dados_ib.get("abertura") is not None else "—"
        al_s = fmt_num(dados_ib["alta"]) if dados_ib.get("alta") is not None else "—"
        bx_s = fmt_num(dados_ib["baixa"]) if dados_ib.get("baixa") is not None else "—"
        a52_s = fmt_num(dados_ib["alt_52s"]) if dados_ib.get("alt_52s") is not None else "—"
        b52_s = fmt_num(dados_ib["bai_52s"]) if dados_ib.get("bai_52s") is not None else "—"

        st.markdown(
            "<div style='display:grid; grid-template-columns:repeat(3,minmax(0,1fr)); gap:4px 12px; "
            "font-size:11px; line-height:1.45; border-top:1px solid rgba(128,128,128,0.20); padding-top:6px; margin-top:2px;'>"
            f"<div style='display:flex; justify-content:space-between;'><span style='opacity:0.7;'>Pré-fech.</span><strong>{pf_s}</strong></div>"
            f"<div style='display:flex; justify-content:space-between;'><span style='opacity:0.7;'>Alta</span><strong>{al_s}</strong></div>"
            f"<div style='display:flex; justify-content:space-between;'><span style='opacity:0.7;'>Alt 52s</span><strong>{a52_s}</strong></div>"
            f"<div style='display:flex; justify-content:space-between;'><span style='opacity:0.7;'>Abertura</span><strong>{ab_s}</strong></div>"
            f"<div style='display:flex; justify-content:space-between;'><span style='opacity:0.7;'>Baixa</span><strong>{bx_s}</strong></div>"
            f"<div style='display:flex; justify-content:space-between;'><span style='opacity:0.7;'>Bai 52s</span><strong>{b52_s}</strong></div>"
            "</div>"
            "<div style='font-size:10px; opacity:0.65; margin-top:4px; text-align:right;'>"
            "💡 DEXTools/TradingView: Shift + Arrastar (ou 📏 Medir) para medir % · Scroll para zoom"
            "</div>",
            unsafe_allow_html=True,
        )


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
    pl_atual = pl_live if pl_live is not None else ((val_merc_atual / lliq_12) if (val_merc_atual and lliq_12 and lliq_12 != 0) else pl_12)
    patr_atual = parse_br_num(det_fund.get("Patrim. Líq")) or ((vpa_12 * acoes_info) if (vpa_12 and acoes_info) else None)
    pvp_atual = pvp_live if pvp_live is not None else ((val_merc_atual / patr_atual) if (val_merc_atual and patr_atual and patr_atual != 0) else pvp_12)
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


DICIONARIO_TERMOS = {
    "IFR (14) / RSI": {
        "categoria": "📊 Análise Técnica",
        "nome_completo": "Índice de Força Relativa (14 dias) / Relative Strength Index",
        "o_que_e": "Um termômetro de 0 a 100 que mede a velocidade e a intensidade das altas e quedas recentes de uma ação nos últimos 14 pregões.",
        "como_interpretar": "Abaixo de 30 indica ativo muito descontado (sobrevendido). Entre 30 e 48 costuma ser uma excelente região de entrada após respiro. Acima de 70 sinaliza euforia/sobrecompra, com maior risco de correção no curto prazo.",
    },
    "MM20": {
        "categoria": "📊 Análise Técnica",
        "nome_completo": "Média Móvel Simples de 20 Dias",
        "o_que_e": "É o preço médio de fechamento da ação nos últimos 20 dias úteis (cerca de 1 mês), indicando a tendência de curtíssimo prazo.",
        "como_interpretar": "Quando a cotação trabalha acima da MM20, há força compradora imediata. Se cair muito rápido abaixo dela, pode indicar perda de fôlego no curto prazo.",
    },
    "MM50": {
        "categoria": "📊 Análise Técnica",
        "nome_completo": "Média Móvel Simples de 50 Dias",
        "o_que_e": "É a média dos preços de fechamento dos últimos 50 pregões (cerca de 2 meses e meio), funcionando como referência de tendência intermediária.",
        "como_interpretar": "Muitas vezes atua como suporte ou resistência natural. Aproximações próximas da MM50 em empresas lucrativas costumam oferecer pontos equilibrados de compra.",
    },
    "MM200": {
        "categoria": "📊 Análise Técnica",
        "nome_completo": "Média Móvel Simples de 200 Dias",
        "o_que_e": "É a grande média de longo prazo do mercado (cerca de 10 meses de pregões), muito usada por investidores institucionais para definir a tendência principal.",
        "como_interpretar": "Preço acima da MM200 indica tendência primária de alta. Preço muito acima (+25% ou mais) pode significar esticamento; abaixo dela indica tendência de baixa ou fase corretiva.",
    },
    "Razão de Volume": {
        "categoria": "📊 Análise Técnica",
        "nome_completo": "Razão entre Volume Médio de 5 Dias e 60 Dias",
        "o_que_e": "Compara quanto dinheiro/ações foram negociados nos últimos 5 dias em relação à média dos últimos 60 dias.",
        "como_interpretar": "Valores acima de 1,3x mostram entrada incomum de fluxo (interesse forte do mercado). Em altas, confirma força compradora; em quedas bruscas, indica pressão vendedora.",
    },
    "Distância da Máxima 52 Semanas": {
        "categoria": "📊 Análise Técnica",
        "nome_completo": "Variação Percentual em Relação ao Topo de 1 Ano",
        "o_que_e": "Mostra quantos porcento a cotação atual está abaixo (ou próxima) do maior preço atingido pela ação nos últimos 12 meses.",
        "como_interpretar": "Descontos moderados entre -10% e -25% em empresas boas costumam abrir boas janelas de compra. Perto de 0% indica que o papel está nas máximas do ano.",
    },
    "P/L": {
        "categoria": "💰 Valuation",
        "nome_completo": "Preço sobre Lucro",
        "o_que_e": "Divide o preço da ação pelo lucro anual por ação. Na prática, estima em quantos anos o lucro da empresa pagaria o valor investido, se tudo fosse distribuído.",
        "como_interpretar": "Quanto menor (desde que positivo), mais barata a ação tende a estar (ex: abaixo de 8x a 10x costuma ser descontado na B3). P/L negativo significa que a empresa teve prejuízo nos últimos 12 meses.",
    },
    "P/VP": {
        "categoria": "💰 Valuation",
        "nome_completo": "Preço sobre Valor Patrimonial",
        "o_que_e": "Compara o preço da ação na Bolsa com o valor contábil líquido dos bens e direitos da empresa (Patrimônio Líquido por ação).",
        "como_interpretar": "Abaixo de 1,0 significa que você está pagando menos pelo papel do que vale o patrimônio líquido da empresa no balanço. Acima de 2,0 exige rentabilidade muito alta para se justificar.",
    },
    "LPA": {
        "categoria": "💰 Valuation",
        "nome_completo": "Lucro por Ação",
        "o_que_e": "É o lucro líquido dos últimos 12 meses dividido pela quantidade total de ações da empresa.",
        "como_interpretar": "Mostra quanto lucro cada ação individual gera. Quanto maior e mais crescente ao longo dos anos, mais saudável tende a ser o negócio.",
    },
    "VPA": {
        "categoria": "💰 Valuation",
        "nome_completo": "Valor Patrimonial por Ação",
        "o_que_e": "É o Patrimônio Líquido da empresa (ativos menos dívidas) dividido pelo número de ações.",
        "como_interpretar": "Funciona como um piso contábil de referência. Quando a cotação está abaixo do VPA, o P/VP fica menor que 1,0.",
    },
    "EV/EBITDA": {
        "categoria": "💰 Valuation",
        "nome_completo": "Enterprise Value sobre EBITDA",
        "o_que_e": "Compara o valor total da firma (valor de mercado + dívida líquida) com a geração de caixa operacional anual antes de juros, impostos e depreciação.",
        "como_interpretar": "Muito útil para comparar empresas com diferentes níveis de dívida. Valores baixos (ex: abaixo de 6x a 8x) sugerem geração de caixa barata. Não se aplica a bancos e seguradoras.",
    },
    "DY (Dividend Yield)": {
        "categoria": "💵 Dividendos & Preços-Teto",
        "nome_completo": "Rendimento de Dividendos (12 meses)",
        "o_que_e": "Mostra o percentual pago em dividendos e JCP nos últimos 12 meses em relação ao preço atual da ação.",
        "como_interpretar": "Para carteiras de renda passiva, yields acima de 6% ao ano costumam ser considerados atrativos. Cuidado apenas com yields pontuais altíssimos vindos de lucros não recorrentes.",
    },
    "DPA (Dividendo por Ação)": {
        "categoria": "💵 Dividendos & Preços-Teto",
        "nome_completo": "Dividendo por Ação (12m, Médio 6a e Projetivo)",
        "o_que_e": "Valor em reais (R$) que cada ação pagou de proventos nos últimos 12 meses, na média anual dos últimos 6 anos ou na estimativa projetada.",
        "como_interpretar": "Serve de base direta para calcular os Preços-Teto de dividendos. Comparar o DPA de 12 meses com a média de 6 anos ajuda a ver se o pagamento atual é sustentável.",
    },
    "Preço-Teto Bazin": {
        "categoria": "💵 Dividendos & Preços-Teto",
        "nome_completo": "Preço-Teto pelo Método Décio Bazin (12 meses)",
        "o_que_e": "Calcula o preço máximo que você deveria pagar por uma ação para garantir pelo menos 6% ao ano em dividendos (DPA 12m ÷ 0,06).",
        "como_interpretar": "Se a cotação atual estiver abaixo do Preço-Teto Bazin, há margem de segurança positiva para renda passiva.",
    },
    "Preço Justo Graham": {
        "categoria": "💵 Dividendos & Preços-Teto",
        "nome_completo": "Valor Intrínseco de Benjamin Graham",
        "o_que_e": "Fórmula clássica criada pelo mentor de Warren Buffett: raiz quadrada de (22,5 × LPA × VPA), equilibrando lucro e patrimônio.",
        "como_interpretar": "Representa uma referência conservadora de valor justo. Comprar com a cotação abaixo do Preço Justo de Graham aumenta a margem de segurança patrimonial.",
    },
    "Preço-Teto Médio (6 anos)": {
        "categoria": "💵 Dividendos & Preços-Teto",
        "nome_completo": "Preço-Teto pela Média de Dividendos de 6 Anos",
        "o_que_e": "Divide a média anual de dividendos pagos nos últimos 6 anos por 6% (0,06), suavizando anos atípicos muito bons ou muito fracos.",
        "como_interpretar": "É uma régua mais estável e rigorosa que o Bazin de 12 meses, ideal para empresas cíclicas ou pagadoras tradicionais de longo prazo.",
    },
    "Preço-Teto Projetivo": {
        "categoria": "💵 Dividendos & Preços-Teto",
        "nome_completo": "Preço-Teto pelo Dividendo Projetado",
        "o_que_e": "Estima o preço máximo para 6% de yield considerando o dividendo projetado com base no lucro recente e histórico de distribuição (payout).",
        "como_interpretar": "Ajuda a olhar para frente quando a empresa aumentou ou reduziu sua capacidade de pagamento recentemente.",
    },
    "Faixa de Preço do Modelo": {
        "categoria": "💵 Dividendos & Preços-Teto",
        "nome_completo": "Teto com Margem de Segurança vs Zona de Sobrepreço",
        "o_que_e": "Define duas faixas de referência: o Teto com Margem (menor valor entre Graham e o Preço-Teto médio de dividendos com 15% de desconto) e a Zona de Sobrepreço calibrada por setor (para Bancos/Seguradoras: menor valor entre Graham e 1,15x o VPA, mínimo +15% sobre o teto; para demais empresas: menor valor entre 1,25x Graham e DY de 4%, mínimo +20% sobre o teto).",
        "como_interpretar": "Abaixo do Teto com Margem o ativo oferece ótimo desconto; entre o Teto e o Sobrepreço está em faixa intermediária; acima da Zona de Sobrepreço o preço já embute pouca margem de segurança.",
    },
    "ROE": {
        "categoria": "🏛️ Eficiência & Dívida",
        "nome_completo": "Return on Equity (Retorno sobre o Patrimônio Líquido)",
        "o_que_e": "Mede quanto de lucro líquido a empresa consegue gerar em relação ao dinheiro próprio dos acionistas (Patrimônio Líquido).",
        "como_interpretar": "Acima de 15% ao ano costuma indicar empresa muito eficiente e com vantagens competitivas. Abaixo de 8% indica baixa rentabilidade; negativo indica prejuízo.",
    },
    "ROIC": {
        "categoria": "🏛️ Eficiência & Dívida",
        "nome_completo": "Return on Invested Capital (Retorno sobre Capital Investido)",
        "o_que_e": "Mede o retorno operacional que a empresa gera usando todo o capital investido no negócio (dinheiro dos sócios + dívidas).",
        "como_interpretar": "Complementa o ROE evitando distorções por excesso de dívida. ROIC acima de 12% a 15% costuma apontar negócios excelentes (não aplicado a bancos).",
    },
    "Margem Líquida": {
        "categoria": "🏛️ Eficiência & Dívida",
        "nome_completo": "Lucro Líquido dividido pela Receita Líquida",
        "o_que_e": "Mostra quantos centavos sobram de lucro limpo para cada R$ 1,00 vendido pela empresa após pagar todos os custos, despesas, juros e impostos.",
        "como_interpretar": "Margens acima de 10% indicam boa folga operacional. Margem negativa significa prejuízo e aciona alerta de risco no painel.",
    },
    "Dívida Líquida / Patrimônio Líquido": {
        "categoria": "🏛️ Eficiência & Dívida",
        "nome_completo": "Endividamento sobre o Patrimônio (e Dív.Brut/Patrim)",
        "o_que_e": "Compara o tamanho das dívidas da empresa com o patrimônio líquido que ela possui. No filtro de risco do painel, também monitora a Dívida Bruta/Patrimônio.",
        "como_interpretar": "Até 1,0x costuma ser confortável. Entre 1,0x e 2,5x pede atenção em juros altos. Acima de 3,0x (para não-bancos) sinaliza alavancagem elevada e aciona a trava de cautela.",
    },
    "Liquidez Corrente": {
        "categoria": "🏛️ Eficiência & Dívida",
        "nome_completo": "Ativo Circulante dividido pelo Passivo Circulante",
        "o_que_e": "Mede a capacidade da empresa de pagar suas contas e dívidas que vencem nos próximos 12 meses usando seu caixa e recebíveis de curto prazo.",
        "como_interpretar": "Acima de 1,5 indica folga financeira tranquila no curto prazo. Abaixo de 1,0 significa que as obrigações de curto prazo superam os recursos imediatos.",
    },
    "Score Geral": {
        "categoria": "🎯 Conceitos do Painel",
        "nome_completo": "Pontuação Combinada do Painel (0 a 100)",
        "o_que_e": "Nota principal equilibrada que combina 60% do Score de Longo Prazo (fundamentos, valuation e saúde) com 40% do Score de Curto Prazo (timing técnico e notícias).",
        "como_interpretar": "Acima de 70 pontos indica forte alinhamento entre empresa boa/barata e bom momento de entrada. Entre 55 e 70 indica equilíbrio razoável.",
    },
    "Score Longo Prazo (LP)": {
        "categoria": "🎯 Conceitos do Painel",
        "nome_completo": "Pontuação de Fundamentos & Dividendos (0 a 100)",
        "o_que_e": "Avalia Valuation com trava de confiança (35 pts), Rentabilidade ROE/ROIC/Margem (30 pts), Saúde Financeira/Dívida/Crescimento (25 pts) e Contexto de Notícias (10 pts).",
        "como_interpretar": "Ideal para quem busca acumular boas ações pensando em anos e dividendos. Possui trava anti-armadilha no teto de 50 pts caso haja prejuízo, dívida crítica ou recuperação judicial.",
    },
    "Score Curto Prazo (CP)": {
        "categoria": "🎯 Conceitos do Painel",
        "nome_completo": "Pontuação de Timing Técnico & Catalisadores (0 a 100)",
        "o_que_e": "Avalia ponto de entrada pelo IFR 14 dias (40 pts), posição nas Médias Móveis e distância da máxima de 52 semanas (25 pts), News Score (25 pts) e Volume Comprador (10 pts).",
        "como_interpretar": "Ajuda a responder se o momento atual do gráfico e das notícias é favorável para comprar agora ou se vale aguardar um respiro.",
    },
    "News Score (Notícias)": {
        "categoria": "🎯 Conceitos do Painel",
        "nome_completo": "Analisador de Sentimento de Notícias (30 dias, -10 a +10)",
        "o_que_e": "Lê manchetes recentes do Google News nos últimos 30 dias (dando peso dobrado para os últimos 7 dias), classificando proventos, lucros, quedas ou riscos críticos.",
        "como_interpretar": "Valores positivos (+2 a +10) indicam catalisadores como dividendos ou lucros fortes; negativos (-2 a -10) alertam sobre ruídos ou resultados fracos.",
    },
    "Vereditos do Modelo": {
        "categoria": "🎯 Conceitos do Painel",
        "nome_completo": "Selos Quantitativos de Classificação (Excelente, Bom, Regular, Indeciso, Esticado, Yield Baixo, Crítico)",
        "o_que_e": "Resumo visual automático que cruza fundamentos, descontos patrimoniais, nível de preço, técnica e notícias.",
        "como_interpretar": "🟢 Excelente: alta atratividade geral. 🔵 Bom (LP ou Desconto Patrimonial): boa tese de acúmulo/valor. 🟡 Regular / Yield Baixo: empresa equilibrada ou barata no patrimônio com dividendo baixo. 🟠 Indeciso: empresa lucrativa com ruído negativo ou sinais mistos. 🟣 Esticado: múltiplos caros acima dos tetos. 🔴 Crítico: prejuízo, dívida >3x ou recuperação judicial.",
    },
}


@st.dialog("📖 Dicionário & Guia de Indicadores da B3")
def modal_dicionario():
    st.caption("Entenda de forma simples e prática o significado de cada sigla, indicador e regra do painel.")
    c_db1, c_db2 = st.columns([2.2, 1.3])
    with c_db1:
        busca_dic = st.text_input(
            "🔍 Pesquisar termo ou conceito...",
            placeholder="Ex: P/L, IFR, Graham, ROE, Dividendos, Esticado...",
            key="dic_busca_input",
        )
    with c_db2:
        cats_dic = ["Todas as categorias"] + list(dict.fromkeys(v["categoria"] for v in DICIONARIO_TERMOS.values()))
        cat_sel = st.selectbox("Tema:", options=cats_dic, key="dic_cat_sel")

    termo_norm = _norm_txt(busca_dic.strip()) if busca_dic else ""
    filtrados = []
    for sigla, info_d in DICIONARIO_TERMOS.items():
        if cat_sel != "Todas as categorias" and info_d["categoria"] != cat_sel:
            continue
        if termo_norm:
            alvo_txt = _norm_txt(
                f"{sigla} {info_d['nome_completo']} {info_d['categoria']} {info_d['o_que_e']} {info_d['como_interpretar']}"
            )
            if termo_norm not in alvo_txt:
                continue
        filtrados.append((sigla, info_d))

    st.caption(f"Mostrando **{len(filtrados)}** de **{len(DICIONARIO_TERMOS)}** termos.")

    if not filtrados:
        st.info("Nenhum termo encontrado para essa pesquisa. Tente palavras como 'lucro', 'IFR', 'dívida' ou 'Graham'.")
    else:
        for sigla, info_d in filtrados:
            with st.expander(f"**{sigla}** — {info_d['nome_completo']}  `{info_d['categoria']}`", expanded=bool(termo_norm)):
                st.markdown(
                    f"<div style='background:rgba(59,130,246,0.10); border-left:4px solid #3b82f6; "
                    f"padding:10px 12px; border-radius:6px; margin-bottom:8px; line-height:1.45;'>"
                    f"<strong>💡 O que é?</strong><br>{html.escape(info_d['o_que_e'])}"
                    f"</div>"
                    f"<div style='background:rgba(34,197,94,0.10); border-left:4px solid #22c55e; "
                    f"padding:10px 12px; border-radius:6px; line-height:1.45;'>"
                    f"<strong>🧭 Como interpretar?</strong><br>{html.escape(info_d['como_interpretar'])}"
                    f"</div>",
                    unsafe_allow_html=True,
                )

    st.divider()
    if st.button("✖️ Fechar Dicionário", type="primary", use_container_width=True, key="btn_fechar_dic"):
        st.rerun()


def badge_veredito_html(veredito: str) -> str:
    estilos = {
        "🟢 Excelente": ("rgba(34,197,94,0.18)", "#22c55e", "rgba(34,197,94,0.45)", "🟢 Excelente"),
        "🔵 Bom (Desconto": ("rgba(59,130,246,0.18)", "#60a5fa", "rgba(59,130,246,0.45)", "🔵 Desc. Patr."),
        "🔵 Bom": ("rgba(59,130,246,0.18)", "#60a5fa", "rgba(59,130,246,0.45)", "🔵 Bom (LP)"),
        "🟣 Esticado": ("rgba(168,85,247,0.18)", "#c084fc", "rgba(168,85,247,0.45)", "🟣 Esticado"),
        "🟠 Indeciso": ("rgba(249,115,22,0.18)", "#fb923c", "rgba(249,115,22,0.45)", "🟠 Indeciso"),
        "🟡 Regular (Yield": ("rgba(234,179,8,0.18)", "#facc15", "rgba(234,179,8,0.45)", "🟡 Yield Baixo"),
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


def _dados_faixa_preco(r: dict) -> dict:
    cot = float(r.get("cotacao") or 0.0)
    teto_m = r.get("preco_teto_modelo")
    sobre_m = r.get("preco_sobrepreco")
    teto_f = float(teto_m) if (teto_m and float(teto_m) > 0.0) else None
    sobre_f = float(sobre_m) if (sobre_m and float(sobre_m) > 0.0) else None

    if teto_f is not None and sobre_f is not None:
        neutro_ini = teto_f + 0.01
        neutro_fim = max(neutro_ini, sobre_f - 0.01)
        z_desc = f"Até R$ {fmt_num(teto_f)}"
        z_neutro = f"De R$ {fmt_num(neutro_ini)} até R$ {fmt_num(neutro_fim)}"
        z_sobre = f"Acima de R$ {fmt_num(sobre_f)}"
    elif teto_f is not None:
        z_desc = f"Até R$ {fmt_num(teto_f)}"
        z_neutro = f"Acima de R$ {fmt_num(teto_f + 0.01)}"
        z_sobre = "Sem referência definida"
    elif sobre_f is not None:
        z_desc = "Sem teto conservador definido"
        z_neutro = f"Até R$ {fmt_num(sobre_f)}"
        z_sobre = f"Acima de R$ {fmt_num(sobre_f)}"
    else:
        z_desc = "Indisponível"
        z_neutro = "Indisponível"
        z_sobre = "Indisponível"

    if teto_f is not None and cot > 0.0 and cot <= teto_f:
        desconto_pct = ((teto_f - cot) / teto_f) * 100.0
        veredito_px = (
            f"Ação com **{fmt_num(desconto_pct, 1)}% de desconto** frente ao teto "
            "(dentro da Zona de Oportunidade 🟢)."
        )
        veredito_px_html = (
            f"Ação com <strong>{fmt_num(desconto_pct, 1)}% de desconto</strong> frente ao teto "
            "(dentro da Zona de Oportunidade 🟢)."
        )
        cor_ver = "#22c55e"
    elif sobre_f is not None and cot > 0.0 and cot > sobre_f:
        sobre_pct = ((cot - sobre_f) / sobre_f) * 100.0
        veredito_px = (
            f"Ação **{fmt_num(sobre_pct, 1)}% acima** da zona segura "
            "(em Zona de Sobrepreço 🔴)."
        )
        veredito_px_html = (
            f"Ação <strong>{fmt_num(sobre_pct, 1)}% acima</strong> da zona segura "
            "(em Zona de Sobrepreço 🔴)."
        )
        cor_ver = "#ef4444"
    elif teto_f is not None or sobre_f is not None:
        veredito_px = "Ação negociada próxima ao valor justo (Zona Neutra 🟡)."
        veredito_px_html = veredito_px
        cor_ver = "#eab308"
    else:
        veredito_px = "Sem dados suficientes de lucro ou dividendos para estimar faixas de preço."
        veredito_px_html = veredito_px
        cor_ver = "#94a3b8"

    setor_norm_fp = _norm_txt(str(r.get("setor_nome") or r.get("setor") or ""))
    eh_banco_seg_fp = bool(r.get("eh_banco_seg", False)) or any(
        k in setor_norm_fp for k in ("banco", "intermediarios financeiros", "seguro", "previdencia")
    )
    regra_sp_lbl = "P/VP 1,15x / Graham · Setor Financeiro" if eh_banco_seg_fp else "DY 4% / Graham 1,25x"

    return {
        "tem_dados": (teto_f is not None or sobre_f is not None),
        "z_desc": z_desc,
        "z_neutro": z_neutro,
        "z_sobre": z_sobre,
        "veredito_px": veredito_px,
        "veredito_px_html": veredito_px_html,
        "cor_ver": cor_ver,
        "eh_banco_seg": eh_banco_seg_fp,
        "regra_sp_lbl": regra_sp_lbl,
    }


def fmt_faixa_preco_modelo(r: dict) -> str:
    d_fp = _dados_faixa_preco(r)
    if not d_fp["tem_dados"]:
        return "🎯 **Faixa de Preço do Modelo:** Indisponível (sem lucro positivo ou histórico suficiente de dividendos)."
    return (
        "🎯 **Faixa de Preço do Modelo:**  \n"
        f"- 🟢 **Zona de Desconto / Oportunidade:** {d_fp['z_desc']} _(Preço sugerido de entrada com margem de segurança)_  \n"
        f"- 🟡 **Zona Neutra / Preço Justo:** {d_fp['z_neutro']}  \n"
        f"- 🔴 **Zona de Sobrepreço / Alerta:** {d_fp['z_sobre']} _(Região de esticamento · {d_fp['regra_sp_lbl']})_  \n"
        f"- 📌 **Veredito do Preço:** {d_fp['veredito_px']}"
    )


def fmt_faixa_preco_html(r: dict) -> str:
    d_fp = _dados_faixa_preco(r)
    if not d_fp["tem_dados"]:
        return (
            "<div style='background:rgba(128,128,128,0.08); border:1px solid rgba(128,128,128,0.22); "
            "border-radius:8px; padding:10px 12px; margin:8px 0; font-size:13px;'>"
            "🎯 <strong>Faixa de Preço do Modelo:</strong> "
            "<span style='opacity:0.8;'>Indisponível (sem lucro positivo ou histórico suficiente de dividendos).</span>"
            "</div>"
        )
    return (
        "<div style='background:rgba(128,128,128,0.07); border:1px solid rgba(128,128,128,0.24); "
        "border-radius:8px; padding:10px 12px; margin:8px 0 10px 0;'>"
        "<div style='font-weight:700; font-size:13px; margin-bottom:8px;'>🎯 Faixa de Preço do Modelo</div>"
        "<div style='display:grid; grid-template-columns:repeat(auto-fit,minmax(200px,1fr)); gap:10px; align-items:stretch; margin-bottom:10px;'>"
        "<div style='background:rgba(34,197,94,0.12); border-left:4px solid #22c55e; border-radius:6px; padding:9px 11px; display:flex; flex-direction:column; justify-content:space-between; min-height:84px;'>"
        "<div style='font-size:11px; font-weight:700; color:#22c55e; line-height:1.3;'>🟢 Zona de Desconto / Oportunidade</div>"
        f"<div style='font-size:15px; font-weight:700; margin:4px 0; line-height:1.25;'>{html.escape(d_fp['z_desc'])}</div>"
        "<div style='font-size:11px; opacity:0.8; line-height:1.3;'>Preço sugerido de entrada com margem de segurança</div>"
        "</div>"
        "<div style='background:rgba(234,179,8,0.12); border-left:4px solid #eab308; border-radius:6px; padding:9px 11px; display:flex; flex-direction:column; justify-content:space-between; min-height:84px;'>"
        "<div style='font-size:11px; font-weight:700; color:#eab308; line-height:1.3;'>🟡 Zona Neutra / Preço Justo</div>"
        f"<div style='font-size:15px; font-weight:700; margin:4px 0; line-height:1.25;'>{html.escape(d_fp['z_neutro'])}</div>"
        "<div style='font-size:11px; opacity:0.8; line-height:1.3;'>Faixa intermediária próxima ao valor justo</div>"
        "</div>"
        "<div style='background:rgba(239,68,68,0.12); border-left:4px solid #ef4444; border-radius:6px; padding:9px 11px; display:flex; flex-direction:column; justify-content:space-between; min-height:84px;'>"
        "<div style='font-size:11px; font-weight:700; color:#ef4444; line-height:1.3;'>🔴 Zona de Sobrepreço / Alerta</div>"
        f"<div style='font-size:15px; font-weight:700; margin:4px 0; line-height:1.25;'>{html.escape(d_fp['z_sobre'])}</div>"
        f"<div style='font-size:11px; opacity:0.8; line-height:1.3;'>Região de esticamento ({html.escape(d_fp['regra_sp_lbl'])})</div>"
        "</div>"
        "</div>"
        f"<div style='font-size:13px; padding:6px 10px; border-radius:6px; background:rgba(128,128,128,0.10); border-left:3px solid {d_fp['cor_ver']};'>"
        f"📌 <strong>Veredito do Preço:</strong> {d_fp['veredito_px_html']}"
        "</div>"
        "</div>"
    )


def gerar_justificativa_detalhada(r: dict, modo: str = "score_geral") -> str:
    m_low = str(modo or "score_geral").lower()
    eh_lp = ("lp" in m_low) or ("longo" in m_low)
    eh_cp = ("cp" in m_low) or ("curto" in m_low)

    cot = float(r.get("cotacao") or 0.0)
    eh_banco_seg = bool(r.get("eh_banco_seg", False))
    eh_value_trap = bool(r.get("eh_value_trap", False))

    score_lp = float(r.get("score_lp") or 0.0)
    score_cp = float(r.get("score_cp") or 0.0)

    pl = r.get("pl")
    pvp = r.get("pvp")
    roe = r.get("roe")
    roic = r.get("roic")
    marg_liq = r.get("marg_liq")
    div_brut_patrim = r.get("div_brut_patrim")
    dy_12m = float(r.get("dy_12m") or 0.0)

    avg_ms = r.get("avg_ms")
    graham = r.get("graham")
    detalhes = r.get("detalhes_score") or {}
    n_metodos = int(detalhes.get("n_metodos") or 0)

    ifr_14 = r.get("ifr_14")
    dist_mm200 = r.get("dist_mm200_pct")
    dist_52s = r.get("dist_max_52s_pct")
    razao_vol = r.get("razao_volume")

    news_score = float(r.get("news_score") or 0.0)
    news_resumo = str(r.get("news_resumo") or "⚪ Neutro")
    news_tem_rj = bool(r.get("news_tem_rj", False))
    top_neg = r.get("top_noticia_neg")
    top_pos = r.get("top_noticia_pos")

    def _fmt_meta_noticia(n: dict) -> str:
        fonte = str(n.get("fonte") or "").strip()
        data_s = str(n.get("data_str") or "").strip()
        if fonte and data_s:
            return f" ({fonte} · {data_s})"
        if fonte:
            return f" ({fonte})"
        if data_s:
            return f" ({data_s})"
        return ""

    def _fmt_item_noticia_html(icone: str, rotulo: str, n: dict) -> str:
        titulo_n = html.escape(str(n.get("titulo") or "").strip())
        meta_n = html.escape(_fmt_meta_noticia(n))
        link_n = str(n.get("link") or "").strip()
        if link_n.startswith(("http://", "https://")):
            href_n = html.escape(link_n, quote=True)
            tit_html = (
                f"<a href='{href_n}' target='_blank' rel='noopener noreferrer' "
                f"style='color:#93c5fd; text-decoration:underline; text-decoration-style:dotted;' "
                f"title='Abrir notícia em nova aba'>'{titulo_n}' ↗</a>"
            )
        else:
            tit_html = f"'{titulo_n}'"
        return f"<div style='margin:2px 0;'>{icone} <strong>{html.escape(rotulo)}:</strong> {tit_html}{meta_n}</div>"

    linhas_news = []
    if top_neg and top_neg.get("titulo"):
        linhas_news.append(
            _fmt_item_noticia_html("🔴", "Notícia Negativa Recente (Pressão de Queda)", top_neg)
        )
    if top_pos and top_pos.get("titulo"):
        linhas_news.append(
            _fmt_item_noticia_html("🟢", "Notícia Positiva Recente (Catalisador de Alta)", top_pos)
        )
    if not linhas_news:
        linhas_news.append(
            "<div>⚪ <strong>Notícias Recentes:</strong> Sem manchetes de forte impacto nos últimos 30 dias.</div>"
        )
    bloco_news_linhas = "".join(linhas_news)

    riscos_trap = []
    if marg_liq is not None and marg_liq < 0:
        riscos_trap.append(f"margem líquida negativa ({fmt_num(marg_liq, 1)}%)")
    if roe is not None and roe < 0:
        riscos_trap.append(f"ROE negativo ({fmt_num(roe, 1)}%)")
    if (not eh_banco_seg) and (div_brut_patrim is not None) and div_brut_patrim > 3.0:
        riscos_trap.append(f"endividamento elevado (Dívida/PL de {fmt_num(div_brut_patrim)}x)")
    if news_tem_rj:
        riscos_trap.append("menção recente a recuperação judicial ou falência nas notícias")

    tem_desc_patr = (
        (pvp is not None and 0.0 < pvp <= 1.0)
        or (graham is not None and graham > 0.0 and cot > 0.0 and cot <= float(graham))
        or (pl is not None and 0.0 < pl <= 8.0 and roe is not None and roe > 0.0)
    )

    if eh_lp:
        partes = []
        if eh_value_trap and riscos_trap:
            partes.append(
                "⚠️ Atenção nos fundamentos: o ativo acionou a trava anti-armadilha (score de longo prazo limitado a 50 pontos) "
                f"em razão de {', '.join(riscos_trap)}."
            )
        else:
            if roe is not None and roe >= 18.0:
                frase_rent = f"Empresa de altíssima rentabilidade, entregando ROE de {fmt_num(roe, 1)}%"
            elif roe is not None and roe >= 12.0:
                frase_rent = f"Negócio sólido e rentável, com ROE consistente de {fmt_num(roe, 1)}%"
            elif roe is not None and roe >= 6.0:
                frase_rent = f"Empresa de rentabilidade moderada, com ROE de {fmt_num(roe, 1)}%"
            elif roe is not None:
                frase_rent = f"Rentabilidade ainda comprimida no momento (ROE de {fmt_num(roe, 1)}%)"
            else:
                frase_rent = "Rentabilidade em acompanhamento pelos múltiplos disponíveis"

            if (not eh_banco_seg) and roic is not None and roic >= 12.0 and marg_liq is not None and marg_liq >= 10.0:
                frase_rent += f", ROIC de {fmt_num(roic, 1)}% e margem líquida saudável de {fmt_num(marg_liq, 1)}%"
            elif marg_liq is not None and marg_liq >= 10.0 and not (eh_banco_seg and marg_liq == 0.0):
                frase_rent += f" e margem líquida saudável de {fmt_num(marg_liq, 1)}%"
            elif marg_liq is not None and 0.0 < marg_liq < 5.0:
                frase_rent += f", porém com margem líquida mais apertada ({fmt_num(marg_liq, 1)}%)"

            if (not eh_banco_seg) and div_brut_patrim is not None:
                if div_brut_patrim <= 0.8:
                    frase_rent += ", aliada a balanço conservador e baixo endividamento"
                elif div_brut_patrim <= 2.0:
                    frase_rent += " e dívida sob controle"
                else:
                    frase_rent += f", embora peça atenção à alavancagem (Dív/PL de {fmt_num(div_brut_patrim)}x)"
            partes.append(frase_rent + ".")

        if avg_ms is not None and avg_ms >= 15.0:
            frase_val = f"Negocia com ampla margem de segurança média de {avg_ms:+.1f}% abaixo dos preços-teto do modelo"
        elif avg_ms is not None and avg_ms > 0.0:
            frase_val = f"Negocia com desconto moderado ({avg_ms:+.1f}%) frente aos preços-teto estimados"
        elif tem_desc_patr:
            det_p = []
            if pvp is not None and 0.0 < pvp <= 1.0:
                det_p.append(f"P/VP de {fmt_num(pvp)}x")
            if graham is not None and graham > 0.0 and cot > 0.0 and cot <= float(graham):
                det_p.append(f"abaixo do valor justo de Graham (R$ {fmt_num(graham)})")
            if pl is not None and 0.0 < pl <= 8.0:
                det_p.append(f"P/L de {fmt_num(pl)}x")
            frase_val = (
                "Mesmo com tetos de dividendos mais contidos, apresenta claro desconto patrimonial "
                f"({', '.join(det_p)})"
            )
        elif avg_ms is not None:
            frase_val = f"Cotação negocia {abs(avg_ms):.1f}% acima da média dos preços-teto do modelo"
        else:
            frase_val = "Cobertura parcial de preços-teto pelos dados atuais"

        if n_metodos == 1:
            frase_val += " (nota: cobertura de apenas 1 método de valuation, aplicando trava de confiança)"
        elif n_metodos == 2:
            frase_val += " (cobertura de 2 métodos de valuation)"
        partes.append(frase_val + ".")

        if dy_12m >= 6.0:
            partes.append(f"Excelente perfil para acúmulo e renda passiva com dividendos de {fmt_num(dy_12m, 1)}% em 12 meses.")
        elif dy_12m >= 3.5:
            partes.append(f"Entrega retorno intermediário em proventos (DY de {fmt_num(dy_12m, 1)}%), equilibrando renda e crescimento.")
        elif dy_12m > 0.0:
            partes.append(f"Dividend yield ainda modesto ({fmt_num(dy_12m, 1)}%), com tese mais apoiada em valor patrimonial/lucro do que em renda imediata.")
        else:
            partes.append("Não distribui dividendos no momento (DY de 0%), zerando a parcela de renda na nota.")

        texto_fundamentos = " ".join(partes)
        return f"📝 **Diagnóstico Técnico & Fundamentalista:** {texto_fundamentos}\n\n{bloco_news_linhas}"

    if eh_cp:
        partes = []
        if ifr_14 is not None:
            if 30.0 <= ifr_14 <= 48.0:
                partes.append(
                    f"Em excelente ponto de entrada técnico: o IFR está em {fmt_num(ifr_14, 1)} "
                    "(região de sobrevenda/respiro favorável para retomada)."
                )
            elif ifr_14 < 30.0:
                partes.append(
                    f"IFR bastante pressionado em {fmt_num(ifr_14, 1)} (sobrevenda acentuada), sugerindo possível exaustão vendedora, "
                    "mas exigindo confirmação de piso antes de acelerar compras."
                )
            elif ifr_14 <= 65.0:
                partes.append(f"O IFR opera em {fmt_num(ifr_14, 1)}, em zona neutra e sem sinais de exaustão.")
            else:
                partes.append(
                    f"Alerta de esticamento no curto prazo: o IFR já marca {fmt_num(ifr_14, 1)} (sobrecompra), "
                    "elevando o risco de realização técnica."
                )
        else:
            partes.append("Leitura de IFR indisponível para este ativo no momento.")

        if dist_mm200 is not None:
            if 0.0 <= dist_mm200 <= 18.0:
                tr_txt = f"O preço segue {dist_mm200:+.1f}% acima da MM200 (tendência primária construtiva)"
            elif dist_mm200 > 18.0:
                tr_txt = f"O preço negocia bem esticado acima da MM200 ({dist_mm200:+.1f}%)"
            elif dist_mm200 >= -12.0:
                tr_txt = f"A cotação testa região próxima abaixo da MM200 ({dist_mm200:+.1f}%)"
            else:
                tr_txt = f"O papel segue {abs(dist_mm200):.1f}% abaixo da MM200, ainda em trajetória corretiva"
            if dist_52s is not None:
                if -25.0 <= dist_52s <= -5.0:
                    tr_txt += f", com desconto de {abs(dist_52s):.1f}% frente à máxima de 52 semanas."
                elif dist_52s > -5.0:
                    tr_txt += ", encostado na máxima de 52 semanas."
                else:
                    tr_txt += f" e {abs(dist_52s):.1f}% distante do topo de 52 semanas."
            else:
                tr_txt += "."
            partes.append(tr_txt)

        if razao_vol is not None and razao_vol >= 1.35:
            partes.append(f"O volume de negócios acelerou ({fmt_num(razao_vol, 2)}x a média de 60 dias), confirmando maior interesse comprador.")

        texto_fundamentos = " ".join(partes)
        return f"📝 **Diagnóstico Técnico & Fundamentalista:** {texto_fundamentos}\n\n{bloco_news_linhas}"

    # Modo Geral (Combinado: Longo Prazo + Curto Prazo)
    if eh_value_trap and riscos_trap:
        base_lp = (
            "⚠️ A tese exige cautela máxima nos fundamentos: a trava anti-armadilha foi acionada devido a "
            f"{', '.join(riscos_trap)}"
        )
    else:
        if score_lp >= 72.0:
            abertura = "Combina números muito fortes de longo prazo"
        elif score_lp >= 58.0:
            abertura = "Apresenta boa consistência fundamentalista"
        else:
            abertura = "Mostra fundamentos mais moderados nesta leitura"

        det_lp = []
        if pl is not None and pl > 0:
            det_lp.append(f"P/L de {fmt_num(pl)}x")
        if roe is not None:
            det_lp.append(f"ROE de {fmt_num(roe, 1)}%")
        if pvp is not None and pvp > 0:
            det_lp.append(f"P/VP de {fmt_num(pvp)}x")
        if dy_12m >= 4.0:
            det_lp.append(f"DY de {fmt_num(dy_12m, 1)}%")

        base_lp = abertura + (f" com {', '.join(det_lp)}" if det_lp else "")
        if avg_ms is not None and avg_ms > 5.0:
            base_lp += f" e margem de segurança média de {avg_ms:+.1f}% nos preços-teto"
        elif tem_desc_patr:
            base_lp += " e negocia com claro desconto patrimonial"
        elif avg_ms is not None and avg_ms < -5.0:
            base_lp += f", embora negocie {abs(avg_ms):.1f}% acima da média dos preços-teto"

    sinais_alerta_cp = []
    if ifr_14 is not None and ifr_14 >= 68.0:
        sinais_alerta_cp.append(f"IFR esticado em {fmt_num(ifr_14, 1)} (sobrecompra)")
    elif ifr_14 is not None and ifr_14 < 30.0:
        sinais_alerta_cp.append(f"IFR fortemente sobrevendido ({fmt_num(ifr_14, 1)})")
    if news_score < 0.0:
        sinais_alerta_cp.append(f"pressão de notícias negativas recentes ({news_score:+.1f} — {news_resumo})")
    if dist_mm200 is not None and dist_mm200 < -12.0:
        sinais_alerta_cp.append(f"preço ainda {abs(dist_mm200):.1f}% abaixo da MM200")

    sinais_pos_cp = []
    if ifr_14 is not None and 30.0 <= ifr_14 <= 48.0:
        sinais_pos_cp.append(f"IFR em ponto técnico atrativo ({fmt_num(ifr_14, 1)})")
    if news_score >= 2.0:
        sinais_pos_cp.append(f"notícias recentes positivas ({news_score:+.1f} — {news_resumo})")
    if razao_vol is not None and razao_vol >= 1.35:
        sinais_pos_cp.append(f"volume em aceleração ({fmt_num(razao_vol, 2)}x)")

    if (not eh_value_trap) and score_lp >= 58.0 and sinais_alerta_cp:
        texto_fundamentos = f"{base_lp}, mas sinaliza cautela temporária no curto prazo devido a {' e '.join(sinais_alerta_cp)}."
    elif sinais_pos_cp and not sinais_alerta_cp:
        texto_fundamentos = f"{base_lp}, somando bom momento no curto prazo com {' e '.join(sinais_pos_cp)}."
    elif sinais_alerta_cp:
        texto_fundamentos = f"{base_lp}, além de registrar {' e '.join(sinais_alerta_cp)} no curto prazo."
    elif ifr_14 is not None:
        texto_fundamentos = f"{base_lp}, mantendo quadro técnico equilibrado (IFR em {fmt_num(ifr_14, 1)}) e sentimento de mercado {news_resumo.lower()}."
    else:
        texto_fundamentos = f"{base_lp}, com sentimento de mercado {news_resumo.lower()}."

    return f"📝 **Diagnóstico Técnico & Fundamentalista:** {texto_fundamentos}\n\n{bloco_news_linhas}"


def render_grafico_e_tabela_ativo(
    ticker: str,
    nome: str = "",
    base_ativo: dict | None = None,
    key_prefix: str = "raiox",
    modo_score_chave: str = "score_geral",
):
    c_tit, c_fav = st.columns([4, 1.3], vertical_alignment="center")
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
        just_r = gerar_justificativa_detalhada(base_ativo, modo_score_chave)
        ifr_txt_r = fmt_num(ifr_r, 1) if ifr_r is not None else "—"
        d200_txt_r = f"{dist_200_r:+.1f}%" if dist_200_r is not None else "—"
        d52_txt_r = f"{dist_52_r:+.1f}%" if dist_52_r is not None else "—"

        pl_r = base_ativo.get("pl")
        pvp_r = base_ativo.get("pvp")
        roe_r = base_ativo.get("roe")
        dy_r = base_ativo.get("dy_12m")
        graham_r = base_ativo.get("graham")
        bazin_r = base_ativo.get("pt_bazin")

        pl_txt_r = fmt_num(pl_r) if pl_r is not None else "—"
        pvp_txt_r = fmt_num(pvp_r) if pvp_r is not None else "—"
        roe_txt_r = f"{fmt_num(roe_r, 1)}%" if roe_r is not None else "—"
        dy_txt_r = f"{fmt_num(dy_r, 1)}%" if dy_r is not None else "—"
        gr_txt_r = f"R$ {fmt_num(graham_r)}" if (graham_r and graham_r > 0) else "—"
        bz_txt_r = f"R$ {fmt_num(bazin_r)}" if (bazin_r and bazin_r > 0) else "—"

        with st.container(border=True):
            st.markdown(
                f"**{pos_r}º Lugar — {ticker}** ({nome or ticker}) | "
                f"Cotação: **R$ {fmt_num(cot_r)}** | "
                f"Score Ativo: **{score_at_r}/100** "
                f"(LP: **{score_lp_r}** | CP: **{score_cp_r}** | News: **{news_sc_r:+.1f}**) | {veredito_r}"
            )
            st.markdown(
                "<div style='display:grid; grid-template-columns:repeat(auto-fit,minmax(145px,1fr)); gap:8px; align-items:stretch; margin:8px 0 10px 0;'>"
                f"<div title='Score de Longo Prazo (0 a 100): avalia Valuation com trava de confiança, Rentabilidade, Saúde Financeira e Notícias.' style='background:rgba(128,128,128,0.10); border:1px solid rgba(128,128,128,0.25); border-radius:8px; padding:9px 11px; cursor:help; display:flex; flex-direction:column; justify-content:space-between; min-height:84px;'>"
                f"<div style='font-size:12px; opacity:0.8; line-height:1.3;'>🏛️ Longo Prazo (LP) ⓘ</div>"
                f"<div style='font-size:20px; font-weight:700; line-height:1.25; margin:2px 0;'>{score_lp_r}/100</div>"
                "<div style='font-size:11px; opacity:0.75; line-height:1.3;'>Fundamentos &amp; Valuation</div></div>"
                f"<div title='Score de Curto Prazo (0 a 100): avalia ponto técnico (IFR), Médias Móveis, Volume e Notícias recentes.' style='background:rgba(128,128,128,0.10); border:1px solid rgba(128,128,128,0.25); border-radius:8px; padding:9px 11px; cursor:help; display:flex; flex-direction:column; justify-content:space-between; min-height:84px;'>"
                f"<div style='font-size:12px; opacity:0.8; line-height:1.3;'>⚡ Curto Prazo (CP) ⓘ</div>"
                f"<div style='font-size:20px; font-weight:700; line-height:1.25; margin:2px 0;'>{score_cp_r}/100</div>"
                "<div style='font-size:11px; opacity:0.75; line-height:1.3;'>Timing &amp; Catalisadores</div></div>"
                f"<div title='News Score (-10 a +10): sentimento das manchetes dos últimos 30 dias com peso dobrado nos últimos 7 dias.' style='background:rgba(128,128,128,0.10); border:1px solid rgba(128,128,128,0.25); border-radius:8px; padding:9px 11px; cursor:help; display:flex; flex-direction:column; justify-content:space-between; min-height:84px;'>"
                f"<div style='font-size:12px; opacity:0.8; line-height:1.3;'>📰 Notícias (30d) ⓘ</div>"
                f"<div style='font-size:20px; font-weight:700; line-height:1.25; margin:2px 0;'>{news_sc_r:+.1f}</div>"
                f"<div style='font-size:11px; opacity:0.85; line-height:1.3;'>{html.escape(news_res_r)}</div></div>"
                f"<div title='IFR 14 dias (RSI): mede força compradora/vendedora (0 a 100). Entre 30 e 48 indica bom ponto de entrada; acima de 70 indica sobrecompra.' style='background:rgba(128,128,128,0.10); border:1px solid rgba(128,128,128,0.25); border-radius:8px; padding:9px 11px; cursor:help; display:flex; flex-direction:column; justify-content:space-between; min-height:84px;'>"
                f"<div style='font-size:12px; opacity:0.8; line-height:1.3;'>📊 IFR (14d) ⓘ</div>"
                f"<div style='font-size:20px; font-weight:700; line-height:1.25; margin:2px 0;'>{ifr_txt_r}</div>"
                f"<div style='font-size:11px; opacity:0.85; line-height:1.3;'>"
                f"<span title='Distância da Média Móvel de 200 dias: indica tendência principal de longo prazo.'>MM200: {d200_txt_r}</span> | "
                f"<span title='Distância da Máxima de 52 semanas: quanto o preço atual está abaixo do topo de 1 ano.'>52s: {d52_txt_r}</span>"
                f"</div></div>"
                "</div>"
                "<div style='display:flex; flex-wrap:wrap; gap:14px; font-size:13px; padding:6px 10px; background:rgba(128,128,128,0.07); border-radius:6px; margin-bottom:8px;'>"
                f"<span title='Preço sobre Lucro: quantos anos o lucro atual levaria para pagar o investimento.' style='cursor:help; border-bottom:1px dotted rgba(128,128,128,0.6);'><strong>P/L:</strong> {pl_txt_r}</span>"
                f"<span title='Preço sobre Valor Patrimonial: compara preço de tela com o patrimônio contábil. Abaixo de 1,0 indica desconto.' style='cursor:help; border-bottom:1px dotted rgba(128,128,128,0.6);'><strong>P/VP:</strong> {pvp_txt_r}</span>"
                f"<span title='Retorno sobre Patrimônio Líquido: eficiência da empresa em gerar lucro com capital próprio.' style='cursor:help; border-bottom:1px dotted rgba(128,128,128,0.6);'><strong>ROE:</strong> {roe_txt_r}</span>"
                f"<span title='Dividend Yield (12m): percentual pago em dividendos e JCP sobre a cotação atual.' style='cursor:help; border-bottom:1px dotted rgba(128,128,128,0.6);'><strong>DY 12m:</strong> {dy_txt_r}</span>"
                f"<span title='Preço-Teto Bazin (12m): DPA de 12 meses dividido por 6%, referência para renda passiva.' style='cursor:help; border-bottom:1px dotted rgba(128,128,128,0.6);'><strong>Bazin:</strong> {bz_txt_r}</span>"
                f"<span title='Preço Justo de Benjamin Graham: valor intrínseco estimado por √(22,5 × LPA × VPA).' style='cursor:help; border-bottom:1px dotted rgba(128,128,128,0.6);'><strong>Graham:</strong> {gr_txt_r}</span>"
                "</div>",
                unsafe_allow_html=True,
            )
            st.markdown(fmt_faixa_preco_html(base_ativo), unsafe_allow_html=True)
            partes_just_rx = just_r.split("\n\n", 1)
            with st.container(border=True):
                st.markdown(f"<div style='padding:2px 2px 4px 2px;'></div>", unsafe_allow_html=True)
                st.markdown(partes_just_rx[0])
                if len(partes_just_rx) > 1 and partes_just_rx[1].strip():
                    st.markdown(
                        "<div style='margin:10px 0 8px 0; border-top:1px solid rgba(128,128,128,0.20);'></div>",
                        unsafe_allow_html=True,
                    )
                    st.markdown(partes_just_rx[1], unsafe_allow_html=True)
        st.markdown("<div style='height:8px;'></div>", unsafe_allow_html=True)

    c_per, c_tipo, c_vis = st.columns([2.6, 1.1, 0.9], vertical_alignment="bottom")
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
    with c_vis:
        estilo_graf = st.selectbox(
            "Estilo:", ["Área", "Candles (DEXTools)"],
            index=0, key=f"{key_prefix}_vis_{ticker}",
        )

    ajustada = tipo_cot == "Cotação ajustada"
    cot_ref_live = float(base_ativo.get("cotacao") or 0.0) if base_ativo else None
    df_ohlcv = buscar_ohlcv_preco(ticker, periodo, ajustada, cot_live=cot_ref_live)
    serie = df_ohlcv["Close"].dropna() if (df_ohlcv is not None and not df_ohlcv.empty and "Close" in df_ohlcv.columns) else pd.Series(dtype=float)

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
        eh_candles = (estilo_graf != "Área") and all(c in df_ohlcv.columns for c in ("Open", "High", "Low", "Close"))

        if eh_candles:
            fig.add_trace(
                go.Candlestick(
                    x=df_ohlcv.index,
                    open=df_ohlcv["Open"],
                    high=df_ohlcv["High"],
                    low=df_ohlcv["Low"],
                    close=df_ohlcv["Close"],
                    name=ticker,
                    increasing_line_color="#22c55e",
                    decreasing_line_color="#ef4444",
                    increasing_fillcolor="#22c55e",
                    decreasing_fillcolor="#ef4444",
                )
            )
            if "Volume" in df_ohlcv.columns and df_ohlcv["Volume"].sum() > 0:
                cores_vol = [
                    "rgba(34,197,94,0.35)" if float(c) >= float(o) else "rgba(239,68,68,0.35)"
                    for o, c in zip(df_ohlcv["Open"], df_ohlcv["Close"])
                ]
                fig.add_trace(
                    go.Bar(
                        x=df_ohlcv.index,
                        y=df_ohlcv["Volume"],
                        name="Volume",
                        marker_color=cores_vol,
                        yaxis="y2",
                        hovertemplate="Vol: %{y:,.0f}<extra></extra>",
                    )
                )
            y_min = float(df_ohlcv["Low"].min())
            y_max = float(df_ohlcv["High"].max())
        else:
            fig.add_trace(
                go.Scatter(
                    x=serie.index, y=serie.values, mode="lines", name=ticker,
                    line=dict(color=cor, width=2.2), fill="tozeroy", fillcolor=fill_cor,
                    hovertemplate=f"{fmt_hover}<br><b>R$ %{{y:.2f}}</b><extra></extra>",
                )
            )
            y_min, y_max = float(serie.min()), float(serie.max())

        margem_y = (y_max - y_min) * 0.09 if y_max > y_min else y_max * 0.05
        layout_kw = dict(
            height=368 if eh_candles else 340,
            margin=dict(l=12, r=76, t=34, b=24),
            paper_bgcolor="rgba(0,0,0,0)",
            plot_bgcolor="rgba(0,0,0,0)",
            showlegend=False,
            hovermode="x unified",
            dragmode="pan",
            xaxis=dict(
                showgrid=True,
                gridcolor="rgba(128,128,128,0.12)",
                zeroline=False,
                rangeslider=dict(visible=False),
                showspikes=True,
                spikemode="across",
                spikesnap="cursor",
                spikethickness=1,
                spikecolor="rgba(148,163,184,0.55)",
                spikedash="dash",
            ),
            yaxis=dict(
                side="right",
                showgrid=True,
                gridcolor="rgba(128,128,128,0.22)",
                tickprefix="R$ ",
                range=[max(0, y_min - (margem_y * (2.2 if eh_candles else 1.0))), y_max + margem_y],
                showspikes=True,
                spikemode="across",
                spikesnap="cursor",
                spikethickness=1,
                spikecolor="rgba(148,163,184,0.55)",
                spikedash="dash",
            ),
            annotations=[
                dict(xref="paper", x=1.01, y=p_fim, xanchor="left", yanchor="middle",
                     text=f"<b>{fmt_num(p_fim)}</b>", showarrow=False,
                     font=dict(color="white", size=12), bgcolor=cor, borderpad=4)
            ],
        )
        if eh_candles and "Volume" in df_ohlcv.columns and df_ohlcv["Volume"].sum() > 0:
            v_max = float(df_ohlcv["Volume"].max())
            layout_kw["yaxis2"] = dict(
                overlaying="y",
                side="left",
                showgrid=False,
                showticklabels=False,
                range=[0, v_max * 5.0 if v_max > 0 else 1],
            )
        fig.update_layout(**layout_kw)
        st.plotly_chart(
            fig,
            use_container_width=True,
            config={"scrollZoom": True, "displaylogo": False, "modeBarButtonsToRemove": ["zoom2d", "zoomIn2d", "zoomOut2d", "lasso2d", "select2d"]},
            key=f"{key_prefix}_plot_{ticker}",
        )
        st.caption("💡 DEXTools: Segure **Shift + Botão Esquerdo e arraste** (ou clique em **📏 Medir**) para medir a variação (%) · Role o mouse para zoom · Arraste para mover.")

        serie_selic_bcb, _ = buscar_historico_selic_bcb()
        serie_max = buscar_serie_max_ajustada(ticker)
        if not serie_max.empty:
            with st.container(border=True):
                s1, s2 = st.columns([1.4, 1.2], vertical_alignment="bottom")
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
                dt_base_ts = (recorte.index[0] if not recorte.empty else serie_max.index[0]).normalize()
                dt_fim_ts = serie_max.index[-1].normalize()
                dias_corridos_sim = max(1, int((dt_fim_ts - dt_base_ts).days))
                data_efetiva = dt_base_ts.strftime("%d/%m/%Y")
                data_final_str = dt_fim_ts.strftime("%d/%m/%Y")

                p_base = float(recorte.iloc[0]) if not recorte.empty else float(serie_max.iloc[0])
                p_hoje = float(serie_max.iloc[-1])
                valor_acao_bruto = valor_inv * (p_hoje / p_base) if p_base > 0 else valor_inv
                ganho_acao = valor_acao_bruto - valor_inv
                if ganho_acao > 0.0 and valor_acao_bruto > 20_000.0:
                    ir_acao = ganho_acao * 0.15
                    valor_acao_liq = valor_acao_bruto - ir_acao
                    nota_ir_acao = f"IR 15% s/ ganho: -R$ {fmt_num(ir_acao)} (venda &gt; R$ 20k/mês) · Bruto: R$ {fmt_num(valor_acao_bruto)}"
                elif ganho_acao > 0.0:
                    ir_acao = 0.0
                    valor_acao_liq = valor_acao_bruto
                    nota_ir_acao = f"IR: Isento (venda ≤ R$ 20k/mês) · Bruto: R$ {fmt_num(valor_acao_bruto)}"
                else:
                    ir_acao = 0.0
                    valor_acao_liq = valor_acao_bruto
                    nota_ir_acao = "IR: Isento (sem lucro tributável no período)"

                ret_acao_pct = ((valor_acao_liq / valor_inv) - 1.0) * 100.0 if valor_inv > 0 else 0.0
                cor_sim = "#22c55e" if valor_acao_liq >= valor_inv else "#ef4444"

                valor_selic_bruto = calcular_selic_calculadora_cidadao(data_efetiva, data_final_str, valor_inv)
                if valor_selic_bruto is None and not serie_selic_bcb.empty:
                    # Convenção oficial da Calculadora do Cidadão: data inicial inclusive, data final exclusive
                    sub_selic = serie_selic_bcb[(serie_selic_bcb.index >= dt_base_ts) & (serie_selic_bcb.index < dt_fim_ts)]
                    fator_selic = float((1.0 + (sub_selic / 100.0)).prod()) if not sub_selic.empty else 1.0
                    valor_selic_bruto = valor_inv * fator_selic

                if valor_selic_bruto is not None:
                    ganho_selic_bruto = max(0.0, valor_selic_bruto - valor_inv)
                    iof_selic, ir_selic, aliq_iof_selic, aliq_ir_selic, imp_selic = _calc_impostos_renda_fixa(ganho_selic_bruto, dias_corridos_sim)
                    excedente_b3 = max(0.0, ((valor_inv + valor_selic_bruto) / 2.0) - 10_000.0)
                    custodia_b3 = excedente_b3 * (((1.0 + 0.002) ** (dias_corridos_sim / 365.0)) - 1.0) if excedente_b3 > 0.0 else 0.0
                    valor_selic_liq = max(0.0, valor_selic_bruto - imp_selic - custodia_b3)
                    ret_selic_pct = ((valor_selic_liq / valor_inv) - 1.0) * 100.0 if valor_inv > 0 else 0.0

                    partes_enc = []
                    if iof_selic > 0.0:
                        partes_enc.append(f"IOF ({fmt_num(aliq_iof_selic, 0)}%): -R$ {fmt_num(iof_selic)}")
                    partes_enc.append(f"IR ({fmt_num(aliq_ir_selic, 1)}%): -R$ {fmt_num(ir_selic)}")
                    if custodia_b3 > 0.0:
                        partes_enc.append(f"B3: -R$ {fmt_num(custodia_b3)}")
                    else:
                        partes_enc.append("B3: Isento (≤R$ 10k)")
                    txt_imp_selic = f"Bruto Calc. Cidadão: R$ {fmt_num(valor_selic_bruto)} · " + " · ".join(partes_enc)

                    card_selic_html = (
                        "<div style='background:rgba(245,158,11,0.10); border:1px solid rgba(245,158,11,0.35); border-radius:8px; padding:12px 14px; "
                        "display:flex; flex-direction:column; justify-content:space-between; align-items:center; text-align:center; min-height:112px;'>"
                        "<div style='font-size:12px; font-weight:600; opacity:0.9; min-height:20px; display:flex; align-items:center; justify-content:center;'>"
                        f"🏛️ No Tesouro Selic (líquido · {data_efetiva} → {data_final_str})"
                        "</div>"
                        "<div style='min-height:34px; display:flex; align-items:baseline; justify-content:center; gap:8px; flex-wrap:wrap; margin:4px 0;'>"
                        f"<strong style='color:#fbbf24; font-size:21px;'>R$ {fmt_num(valor_selic_liq)}</strong>"
                        f"<span style='font-size:13px; font-weight:600; color:#fbbf24;'>({ret_selic_pct:+.2f}%)</span>"
                        "</div>"
                        f"<div style='font-size:11px; opacity:0.82; min-height:30px; display:flex; align-items:center; justify-content:center; line-height:1.35;'>{txt_imp_selic}</div>"
                        "</div>"
                    )
                    diff_sim = valor_acao_liq - valor_selic_liq
                    diff_pp = ret_acao_pct - ret_selic_pct
                    if diff_sim >= 0.0:
                        resumo_sim_html = (
                            f"<div style='margin-top:8px; padding:6px 10px; border-radius:6px; background:rgba(34,197,94,0.12); "
                            f"border-left:3px solid #22c55e; font-size:12.5px;'>"
                            f"🏆 <strong>{ticker}</strong> entregou <strong>R$ {fmt_num(diff_sim)}</strong> ({diff_pp:+.2f} p.p.) a mais que o Tesouro Selic (Calculadora do Cidadão) "
                            f"(já descontando impostos e custódia nos dois casos)."
                            f"</div>"
                        )
                    else:
                        resumo_sim_html = (
                            f"<div style='margin-top:8px; padding:6px 10px; border-radius:6px; background:rgba(245,158,11,0.12); "
                            f"border-left:3px solid #f59e0b; font-size:12.5px;'>"
                            f"🏛️ O <strong>Tesouro Selic (Calculadora do Cidadão)</strong> entregou <strong>R$ {fmt_num(abs(diff_sim))}</strong> ({abs(diff_pp):.2f} p.p.) a mais que {ticker} no período "
                            f"(já descontando impostos e custódia nos dois casos)."
                            f"</div>"
                        )
                else:
                    card_selic_html = (
                        "<div style='background:rgba(128,128,128,0.10); border:1px solid rgba(128,128,128,0.28); border-radius:8px; padding:12px 14px; "
                        "display:flex; flex-direction:column; justify-content:space-between; align-items:center; text-align:center; min-height:112px;'>"
                        "<div style='font-size:12px; font-weight:600; opacity:0.9;'>🏛️ No Tesouro Selic (líquido)</div>"
                        "<div style='font-size:13px; opacity:0.75;'>Indisponível no momento</div>"
                        "<div style='font-size:11px; opacity:0.7;'>API do Banco Central temporariamente indisponível.</div>"
                        "</div>"
                    )
                    resumo_sim_html = ""

                st.markdown(
                    "<div style='display:grid; grid-template-columns:repeat(auto-fit,minmax(240px,1fr)); gap:12px; align-items:stretch; margin-top:6px;'>"
                    "<div style='background:rgba(128,128,128,0.10); border:1px solid rgba(128,128,128,0.28); border-radius:8px; padding:12px 14px; "
                    "display:flex; flex-direction:column; justify-content:space-between; align-items:center; text-align:center; min-height:112px;'>"
                    "<div style='font-size:12px; font-weight:600; opacity:0.9; min-height:20px; display:flex; align-items:center; justify-content:center;'>"
                    f"📈 Em {ticker} (líquido · {data_efetiva} → {data_final_str})"
                    "</div>"
                    "<div style='min-height:34px; display:flex; align-items:baseline; justify-content:center; gap:8px; flex-wrap:wrap; margin:4px 0;'>"
                    f"<strong style='color:{cor_sim}; font-size:21px;'>R$ {fmt_num(valor_acao_liq)}</strong>"
                    f"<span style='font-size:13px; font-weight:600; color:{cor_sim};'>({ret_acao_pct:+.2f}%)</span>"
                    "</div>"
                    f"<div style='font-size:11px; opacity:0.82; min-height:30px; display:flex; align-items:center; justify-content:center; line-height:1.35;'>{nota_ir_acao} · Reinvestindo dividendos</div>"
                    "</div>"
                    f"{card_selic_html}"
                    "</div>"
                    f"{resumo_sim_html}",
                    unsafe_allow_html=True,
                )

    # --- SIMULADOR DE RENDA PASSIVA, SAZONALIDADE DE DIVIDENDOS & CHECKLIST BUY & HOLD ---
    if base_ativo:
        _, selic_aa_atual = buscar_historico_selic_bcb()
        cot_sim = float(base_ativo.get("cotacao") or 0.0)
        if cot_sim <= 0.0 and not serie.empty:
            cot_sim = float(serie.iloc[-1])

        with st.container(border=True):
            st.markdown(f"#### 💰 Simulador de Renda Passiva — {ticker}")
            sr_in1, sr_in2 = st.columns([1.35, 2.65], vertical_alignment="bottom")
            with sr_in1:
                meta_mensal = st.number_input(
                    "Meta de Proventos Mensal desejada com este ativo (R$):",
                    min_value=10.0,
                    value=1000.0,
                    step=100.0,
                    format="%.2f",
                    key=f"{key_prefix}_meta_renda_{ticker}",
                )
            with sr_in2:
                selic_badge_txt = f"Selic atual (BCB): {fmt_num(selic_aa_atual, 2)}% a.a." if selic_aa_atual else "Selic atual: indisponível"
                regra_div_txt = (
                    "Acima de R$ 50 mil/mês por empresa aplica 10% IRRF (Lei 15.270/2025)"
                    if meta_mensal > 50_000.0
                    else "Dividendos isentos de IR até R$ 50 mil/mês por empresa"
                )
                st.markdown(
                    "<style>"
                    "div[data-testid='stElementContainer']:has(.selic-info-pill),"
                    "div[data-testid='stMarkdownContainer']:has(.selic-info-pill){margin:0!important;padding:0!important;}"
                    "</style>"
                    "<div class='selic-info-pill' style='background:rgba(128,128,128,0.09); border:1px solid rgba(128,128,128,0.24); border-radius:8px; "
                    "padding:10px 14px; min-height:44px; box-sizing:border-box; display:flex; align-items:center; justify-content:space-between; gap:10px; flex-wrap:wrap; font-size:12px;'>"
                    f"<span>🏛️ <strong>{selic_badge_txt}</strong></span>"
                    f"<span style='opacity:0.85;'>⚖️ {regra_div_txt}</span>"
                    "</div>",
                    unsafe_allow_html=True,
                )

            dpa_proj_s = base_ativo.get("dpa_proj")
            dpa_12m_s = base_ativo.get("dpa_12m")
            dy_s = float(base_ativo.get("dy_12m") or 0.0)
            if dpa_proj_s and float(dpa_proj_s) > 0:
                dpa_base_sim = float(dpa_proj_s)
            elif dpa_12m_s and float(dpa_12m_s) > 0:
                dpa_base_sim = float(dpa_12m_s)
            elif cot_sim > 0 and dy_s > 0:
                dpa_base_sim = cot_sim * (dy_s / 100.0)
            else:
                dpa_base_sim = 0.0

            if selic_aa_atual and selic_aa_atual > 0:
                cap_selic_15 = _calc_tesouro_selic_capital_mensal(meta_mensal, selic_aa_atual, 0.15)
                cap_selic_225 = _calc_tesouro_selic_capital_mensal(meta_mensal, selic_aa_atual, 0.225)
                nota_b3_rp = " + B3 0,20% (>10k)" if cap_selic_15 > 10_000.0 else " · Isento B3 (≤10k)"
                card_selic_rp = (
                    "<div style='background:rgba(245,158,11,0.10); border:1px solid rgba(245,158,11,0.35); border-radius:8px; padding:12px 14px; "
                    "display:flex; flex-direction:column; justify-content:space-between; align-items:center; text-align:center; min-height:112px;'>"
                    "<div style='font-size:12px; opacity:0.88; min-height:22px; display:flex; align-items:center; justify-content:center;'>"
                    "🏛️ Capital no Tesouro Selic Hoje"
                    "</div>"
                    "<div style='min-height:36px; display:flex; align-items:center; justify-content:center; margin:4px 0;'>"
                    f"<span style='font-size:21px; font-weight:700; color:#fbbf24;'>R$ {fmt_num(cap_selic_15)}</span>"
                    "</div>"
                    "<div style='font-size:11px; opacity:0.82; min-height:32px; display:flex; align-items:center; justify-content:center; line-height:1.35;'>"
                    f"Líq. 15% IR (&gt;2a){nota_b3_rp} · c/ 22,5% IR (≤6m): R$ {fmt_num(cap_selic_225)}"
                    "</div>"
                    "</div>"
                )
            else:
                cap_selic_15 = None
                card_selic_rp = (
                    "<div style='background:rgba(128,128,128,0.10); border:1px solid rgba(128,128,128,0.28); border-radius:8px; padding:12px 14px; "
                    "display:flex; flex-direction:column; justify-content:space-between; align-items:center; text-align:center; min-height:112px;'>"
                    "<div style='font-size:12px; opacity:0.88; min-height:22px; display:flex; align-items:center; justify-content:center;'>🏛️ Capital no Tesouro Selic Hoje</div>"
                    "<div style='font-size:14px; opacity:0.75; min-height:36px; display:flex; align-items:center; justify-content:center;'>Indisponível</div>"
                    "<div style='font-size:11px; opacity:0.7; min-height:32px; display:flex; align-items:center; justify-content:center;'>Taxa Selic do BCB indisponível.</div>"
                    "</div>"
                )

            if dpa_base_sim <= 0.0 or cot_sim <= 0.0:
                qtd_acoes_nec = 0
                st.markdown(
                    "<div style='display:grid; grid-template-columns:repeat(auto-fit,minmax(220px,1fr)); gap:12px; align-items:stretch; margin-top:8px;'>"
                    "<div style='background:rgba(59,130,246,0.10); border:1px solid rgba(59,130,246,0.30); border-radius:8px; padding:12px 14px; "
                    "display:flex; flex-direction:column; justify-content:space-between; align-items:center; text-align:center; min-height:112px;'>"
                    f"<div style='font-size:12px; opacity:0.88; min-height:22px; display:flex; align-items:center; justify-content:center;'>📌 Em {ticker}</div>"
                    "<div style='font-size:14px; opacity:0.8; min-height:36px; display:flex; align-items:center; justify-content:center;'>Sem proventos base</div>"
                    f"<div style='font-size:11px; opacity:0.75; min-height:32px; display:flex; align-items:center; justify-content:center;'>{ticker} não possui histórico ou projeção de proventos positivos.</div>"
                    "</div>"
                    f"{card_selic_rp}"
                    "</div>",
                    unsafe_allow_html=True,
                )
            else:
                eh_acima_50k = meta_mensal > 50_000.0
                meta_anual_liq = meta_mensal * 12.0
                meta_anual_bruta = (meta_mensal / 0.90) * 12.0 if eh_acima_50k else meta_anual_liq
                qtd_acoes_nec = math.ceil(meta_anual_bruta / dpa_base_sim)
                custo_total_nec = qtd_acoes_nec * cot_sim
                dy_impl_sim = (dpa_base_sim / cot_sim) * 100.0
                nota_ir_acao_rp = "Já c/ 10% IRRF (&gt;R$50k/mês)" if eh_acima_50k else "Isento IR (≤R$50k/mês)"

                st.markdown(
                    "<div style='display:grid; grid-template-columns:repeat(auto-fit,minmax(210px,1fr)); gap:12px; align-items:stretch; margin-top:8px;'>"
                    "<div style='background:rgba(59,130,246,0.12); border:1px solid rgba(59,130,246,0.35); border-radius:8px; padding:12px 14px; "
                    "display:flex; flex-direction:column; justify-content:space-between; align-items:center; text-align:center; min-height:112px;'>"
                    "<div style='font-size:12px; opacity:0.88; min-height:22px; display:flex; align-items:center; justify-content:center;'>📌 Ações Necessárias</div>"
                    "<div style='min-height:36px; display:flex; align-items:center; justify-content:center; margin:4px 0;'>"
                    f"<span style='font-size:21px; font-weight:700; color:#60a5fa;'>{fmt_num(qtd_acoes_nec, 0)} ações</span>"
                    "</div>"
                    "<div style='font-size:11px; opacity:0.82; min-height:32px; display:flex; align-items:center; justify-content:center; line-height:1.35;'>"
                    f"Meta anual líq.: R$ {fmt_num(meta_anual_liq)} · DPA: R$ {fmt_num(dpa_base_sim)}"
                    "</div>"
                    "</div>"
                    "<div style='background:rgba(34,197,94,0.12); border:1px solid rgba(34,197,94,0.35); border-radius:8px; padding:12px 14px; "
                    "display:flex; flex-direction:column; justify-content:space-between; align-items:center; text-align:center; min-height:112px;'>"
                    "<div style='font-size:12px; opacity:0.88; min-height:22px; display:flex; align-items:center; justify-content:center;'>💵 Total a Investir na Ação</div>"
                    "<div style='min-height:36px; display:flex; align-items:center; justify-content:center; margin:4px 0;'>"
                    f"<span style='font-size:21px; font-weight:700; color:#22c55e;'>R$ {fmt_num(custo_total_nec)}</span>"
                    "</div>"
                    "<div style='font-size:11px; opacity:0.82; min-height:32px; display:flex; align-items:center; justify-content:center; line-height:1.35;'>"
                    f"Cotação: R$ {fmt_num(cot_sim)} · Yield: {fmt_num(dy_impl_sim, 2)}% · {nota_ir_acao_rp}"
                    "</div>"
                    "</div>"
                    f"{card_selic_rp}"
                    "</div>",
                    unsafe_allow_html=True,
                )

                if cap_selic_15 and cap_selic_15 > 0:
                    diff_cap_rp = custo_total_nec - cap_selic_15
                    if diff_cap_rp <= 0:
                        st.markdown(
                            f"<div style='margin-top:8px; padding:6px 10px; border-radius:6px; background:rgba(34,197,94,0.12); "
                            f"border-left:3px solid #22c55e; font-size:12.5px;'>"
                            f"💡 Pelo yield atual de <strong>{ticker}</strong>, você precisa de <strong>R$ {fmt_num(abs(diff_cap_rp))}</strong> a menos que no Tesouro Selic (com IR de 15% e custódia B3) para receber R$ {fmt_num(meta_mensal)}/mês líquidos."
                            f"</div>",
                            unsafe_allow_html=True,
                        )
                    else:
                        st.markdown(
                            f"<div style='margin-top:8px; padding:6px 10px; border-radius:6px; background:rgba(245,158,11,0.12); "
                            f"border-left:3px solid #f59e0b; font-size:12.5px;'>"
                            f"💡 Hoje, o <strong>Tesouro Selic</strong> exige <strong>R$ {fmt_num(diff_cap_rp)}</strong> a menos de capital inicial que <strong>{ticker}</strong> (já descontando 15% de IR &gt;2a e custódia B3); porém ações tendem a reajustar proventos pela inflação no longo prazo."
                            f"</div>",
                            unsafe_allow_html=True,
                        )

            if dpa_base_sim > 0.0 and st.session_state.get("usuario_email") and st.session_state.get("lancamentos"):
                pos_usr_rx = consolidar_carteira_por_ativo(st.session_state["lancamentos"])
                if ticker in pos_usr_rx and pos_usr_rx[ticker]["qtd"] > 0:
                    qtd_pos_rx = float(pos_usr_rx[ticker]["qtd"])
                    pct_meta_rx = (qtd_pos_rx / qtd_acoes_nec) * 100.0 if qtd_acoes_nec > 0 else 0.0
                    qtd_pos_fmt = int(qtd_pos_rx) if qtd_pos_rx.is_integer() else qtd_pos_rx
                    st.progress(min(1.0, max(0.0, pct_meta_rx / 100.0)))
                    st.markdown(
                        f"🎯 Você já possui **{fmt_num(qtd_pos_fmt, 0)} ações** "
                        f"(**{fmt_num(pct_meta_rx, 1)}%** da sua meta alcançada nesta empresa!)."
                    )

        st.markdown("<div style='height:10px;'></div>", unsafe_allow_html=True)
        col_saz, col_bh = st.columns([1.05, 1.15])
        with col_saz:
            with st.container(border=True):
                st.markdown(f"#### 📅 Sazonalidade de Proventos — {ticker}")
                meses_nomes = ["JAN", "FEV", "MAR", "ABR", "MAI", "JUN", "JUL", "AGO", "SET", "OUT", "NOV", "DEZ"]
                meses_pag = set(base_ativo.get("meses_dividendos") or [])
                pilulas_meses = []
                for idx_m, nome_m in enumerate(meses_nomes, start=1):
                    if idx_m in meses_pag:
                        pilulas_meses.append(
                            f"<div style='text-align:center; padding:6px 4px; border-radius:6px; font-size:12px; font-weight:700; "
                            f"background:rgba(34,197,94,0.18); border:1px solid rgba(34,197,94,0.50); color:#22c55e;'>🟢 {nome_m}</div>"
                        )
                    else:
                        pilulas_meses.append(
                            f"<div style='text-align:center; padding:6px 4px; border-radius:6px; font-size:12px; font-weight:500; "
                            f"background:rgba(128,128,128,0.08); border:1px solid rgba(128,128,128,0.20); opacity:0.60;'>⚪ {nome_m}</div>"
                        )
                st.markdown(
                    "<div style='display:grid; grid-template-columns:repeat(4,1fr); gap:6px; margin:8px 0 10px 0;'>"
                    + "".join(pilulas_meses)
                    + "</div>",
                    unsafe_allow_html=True,
                )
                if meses_pag:
                    st.caption("Meses em que a empresa historicamente costuma pagar proventos (últimos 4 anos).")
                else:
                    st.caption("Meses em que a empresa historicamente costuma pagar proventos (sem registros recentes no Yahoo Finance).")

        with col_bh:
            with st.container(border=True):
                st.markdown(f"#### 🛡️ Checklist Buy & Hold — {ticker}")
                eh_bco_bh = bool(base_ativo.get("eh_banco_seg", False))
                roe_bh = base_ativo.get("roe")
                ml_bh = base_ativo.get("marg_liq")
                div_bh = base_ativo.get("div_brut_patrim")
                pl_bh = base_ativo.get("pl")
                liq2m_bh = float(base_ativo.get("liq_2m") or 0.0)
                consec_bh = int(base_ativo.get("anos_divs_consec") or base_ativo.get("anos_hist") or 0)
                graham_bh = base_ativo.get("graham")
                bazin_bh = base_ativo.get("pt_bazin")

                c1_ok = (roe_bh is not None and roe_bh >= 10.0) if eh_bco_bh else (roe_bh is not None and roe_bh >= 12.0)
                c1_det = f"ROE: {fmt_num(roe_bh, 1)}%" if roe_bh is not None else "ROE indisponível"

                c2_ok = (
                    (ml_bh is not None and ml_bh >= 10.0)
                    or (eh_bco_bh and (ml_bh is None or ml_bh == 0.0 or ml_bh >= 5.0) and (roe_bh is not None and roe_bh >= 10.0) and (pl_bh is None or pl_bh > 0.0) and liq2m_bh >= 1_000_000)
                )
                c2_det = "Banco de grande porte / lucrativo" if (eh_bco_bh and (ml_bh is None or ml_bh == 0.0)) else (f"Margem Líq.: {fmt_num(ml_bh, 1)}%" if ml_bh is not None else "Margem indisponível")

                c3_ok = True if eh_bco_bh else (div_bh is not None and div_bh <= 1.5)
                c3_det = "Intermediário Financeiro / Seguradora" if eh_bco_bh else (f"Dív.Brut/Patrim: {fmt_num(div_bh)}x" if div_bh is not None else "Dívida indisponível")

                c4_ok = consec_bh > 3
                c4_det = f"{consec_bh} ano(s) consecutivo(s) recente(s)"

                abaixo_gr = cot_sim > 0 and graham_bh is not None and graham_bh > 0 and cot_sim < float(graham_bh)
                abaixo_bz = cot_sim > 0 and bazin_bh is not None and bazin_bh > 0 and cot_sim < float(bazin_bh)
                c5_ok = abaixo_gr or abaixo_bz
                tetos_ok = [x for x in ("Graham" if abaixo_gr else "", "Bazin" if abaixo_bz else "") if x]
                c5_det = f"Abaixo de {', '.join(tetos_ok)}" if tetos_ok else "Acima dos tetos de Graham e Bazin"

                criterios_bh = [
                    ("Lucratividade (ROE ≥ 12% ou ≥ 10% bancos)", c1_ok, c1_det),
                    ("Margem Líquida Saudável (≥ 10% ou Banco grande)", c2_ok, c2_det),
                    ("Dívida Sob Controle (Dív/PL ≤ 1,5x ou Banco)", c3_ok, c3_det),
                    ("Histórico de Dividendos (> 3 anos consecutivos)", c4_ok, c4_det),
                    ("Margem de Segurança (< Graham ou Bazin)", c5_ok, c5_det),
                ]
                nota_bh = sum(1 for _, ok_c, _ in criterios_bh if ok_c)
                estrelas_str = ("⭐️" * nota_bh) + ("☆" * (5 - nota_bh))
                selos_bh = {
                    5: "Empresa Fortaleza / Grau de Investimento",
                    4: "Ótima Qualidade Buy & Hold",
                    3: "Qualidade Intermediária (Acompanhar)",
                    2: "Atenção aos Fundamentos",
                    1: "Perfil Frágil para Buy & Hold",
                    0: "Alto Risco / Fora dos Critérios",
                }
                st.markdown(f"**{estrelas_str} {nota_bh}/5 — {selos_bh[nota_bh]}**")
                linhas_bh_html = []
                for tit_c, ok_c, det_c in criterios_bh:
                    ic_c = "<span style='color:#22c55e; font-weight:700;'>[✓]</span>" if ok_c else "<span style='color:#ef4444; font-weight:700;'>[✗]</span>"
                    linhas_bh_html.append(
                        f"<div style='font-size:13px; margin:4px 0;'>{ic_c} <strong>{tit_c}</strong> <span style='opacity:0.78;'>({html.escape(det_c)})</span></div>"
                    )
                st.markdown("".join(linhas_bh_html), unsafe_allow_html=True)

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
            ".hist-wrap{width:100%;overflow-x:auto;overflow-y:hidden;margin:12px 0;}"
            ".hist-table{width:100%;border-collapse:collapse;font-size:13px;text-align:center;}"
            ".hist-table th{background-color:rgba(128,128,128,0.18);padding:10px 8px;border-bottom:2px solid rgba(128,128,128,0.35);font-weight:600;white-space:nowrap;}"
            ".hist-table td{padding:9px 8px;border-bottom:1px solid rgba(128,128,128,0.2);white-space:nowrap;}"
            ".hist-table tr:hover td{background-color:rgba(128,128,128,0.08);}"
            "</style>"
        )
        html_h = (
            f"{css_h}<div class='hist-wrap'><table class='hist-table'><thead><tr>"
            "<th title='Ano do exercício fiscal, ÚLT. 12M (acumulado 12 meses), MÉDIA histórica e ATUAL'>Ano</th>"
            "<th title='Preço sobre Lucro: quantos anos o lucro do período levaria para pagar o valor de mercado'>P/L</th>"
            "<th title='Preço sobre Valor Patrimonial: valor de mercado dividido pelo patrimônio líquido'>P/VP</th>"
            "<th title='Valor Patrimonial por Ação: patrimônio líquido dividido pelo número de ações'>VPA</th>"
            "<th title='Dívida Líquida: empréstimos e financiamentos menos caixa e aplicações financeiras'>Dívida líquida</th>"
            "<th title='Margem Líquida: percentual da receita líquida que vira lucro líquido'>Margem líquida</th>"
            "<th title='EBITDA: geração de caixa operacional antes de juros, impostos, depreciação e amortização'>EBITDA</th>"
            "<th title='Preço sobre EBITDA: valor de mercado dividido pela geração de caixa operacional'>P/EBITDA</th>"
            "<th title='Valor de Mercado: cotação multiplicada pelo total de ações'>Valor de mercado</th>"
            "<th title='Lucro Líquido atribuído aos controladores no período'>Lucro Líq.</th>"
            "<th title='Lucro Bruto: receita líquida menos o custo dos bens ou serviços vendidos'>Lucro Br.</th>"
            "<th title='Receita Líquida: faturamento total descontando impostos sobre vendas e devoluções'>Receita Líq.</th>"
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
    setor_norm_d = _norm_txt(str(d.get("setor_nome") or d.get("setor") or ""))
    eh_banco_seg = bool(d.get("eh_banco_seg", False)) or any(
        k in setor_norm_d for k in ("banco", "intermediarios financeiros", "seguro", "previdencia")
    )

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
    news_tem_rj = bool(d.get("news_tem_rj", False)) or ("/ RJ" in news_resumo)

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

    if eh_banco_seg:
        vpa_val = d.get("vpa")
        teto_patrimonial = (float(vpa_val) * 1.15) if (vpa_val is not None and float(vpa_val) > 0) else None
        if graham and graham > 0:
            if teto_patrimonial is not None:
                preco_sobrepreco = min(float(graham), teto_patrimonial)
            else:
                preco_sobrepreco = float(graham) * 1.10
        elif teto_patrimonial is not None:
            preco_sobrepreco = teto_patrimonial
        else:
            preco_sobrepreco = p_yield_4pct
        if preco_sobrepreco is not None and preco_teto_modelo is not None and preco_teto_modelo > 0:
            preco_sobrepreco = max(preco_teto_modelo * 1.15, preco_sobrepreco)
    else:
        cands_sp = [x for x in (p_yield_4pct, p_graham_125) if x is not None]
        preco_sobrepreco = min(cands_sp) if cands_sp else None
        if preco_sobrepreco is not None and preco_teto_modelo is not None and preco_teto_modelo > 0:
            preco_sobrepreco = max(preco_teto_modelo * 1.20, preco_sobrepreco)

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

    # Trava Anti-Armadilha (Value Trap — Regra Universal de Solvência)
    armadilha_motivos = []
    if marg_liq is not None and marg_liq < 0:
        armadilha_motivos.append(f"margem líquida negativa ({fmt_num(marg_liq, 1)}%)")
    if roe is not None and roe < 0:
        armadilha_motivos.append(f"ROE negativo ({fmt_num(roe, 1)}%)")
    if (not eh_banco_seg) and (div_brut_patrim is not None) and div_brut_patrim > 3.0:
        armadilha_motivos.append(f"Dív/Patrim elevada ({fmt_num(div_brut_patrim)}x > 3,0x)")
    if news_tem_rj:
        armadilha_motivos.append("menção comprovada a recuperação judicial / falência")

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

    # === 4) VEREDITO QUANTITATIVO DO MODELO (BLINDAGEM UNIVERSAL) ===
    if eh_banco_seg and (marg_liq is None or marg_liq == 0.0):
        lucro_solido = (roe is not None and roe >= 10.0) and (pl is None or pl > 0.0)
    else:
        lucro_solido = (roe is not None and roe >= 10.0) and (marg_liq is not None and marg_liq >= 5.0)

    cond_pvp_desc = (pvp is not None and 0.0 < pvp <= 1.0)
    cond_graham_desc = (graham is not None and graham > 0.0 and cot > 0.0 and cot <= float(graham))
    cond_pl_desc = (pl is not None and 0.0 < pl <= 8.0 and roe is not None and roe > 0.0)
    tem_desconto_patrimonial = cond_pvp_desc or cond_graham_desc or cond_pl_desc

    multiplos_esticados = (
        (pvp is not None and pvp > 1.25)
        or (pl is not None and pl > 16.0)
        or (ifr_14 is not None and ifr_14 >= 68.0)
    )
    acima_media_tetos = (avg_ms_real is not None and avg_ms_real < 0.0)
    esta_esticado = (not tem_desconto_patrimonial) and multiplos_esticados and acima_media_tetos

    div_baixo_ou_distorcido = (
        dy_12m < 4.5
        or (div_teto_ref is None)
        or (cot > 0.0 and float(div_teto_ref) < cot)
    )

    if eh_value_trap:
        veredito = "🔴 Crítico (Risco Alto)"
    elif lucro_solido and news_score < 0.0:
        veredito = "🟠 Indeciso (Sinais Mistos)"
    elif esta_esticado:
        veredito = "🟣 Esticado (Alerta Topo/Sobrepreço)"
    elif score_geral >= 72.0 and score_lp >= 70.0 and (avg_ms_real is None or avg_ms_real > 0.0):
        veredito = "🟢 Excelente (Forte Atratividade)"
    elif score_lp >= 62.0 and score_geral >= 58.0:
        if tem_desconto_patrimonial and div_baixo_ou_distorcido:
            veredito = "🔵 Bom (Desconto Patrimonial)"
        else:
            veredito = "🔵 Bom (Acúmulo LP)"
    elif tem_desconto_patrimonial:
        if score_lp >= 55.0 and (cond_pvp_desc or cond_graham_desc):
            veredito = "🔵 Bom (Desconto Patrimonial)"
        elif div_baixo_ou_distorcido:
            veredito = "🟡 Regular (Yield Baixo)"
        else:
            veredito = "🟡 Regular (Neutro)"
    elif abs(score_lp - score_cp) >= 20.0 or news_score <= -2.5 or (score_cp >= 65.0 and score_lp < 55.0):
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
c_hdr_esq, c_hdr_dir = st.columns([1.22, 1.0], vertical_alignment="top")
with c_hdr_esq:
    st.title("📊 Painel Completo da B3 — Valuation, Raio-X & Carteira")
    st.caption("Busca ao vivo, Setor BESST, Favoritos por usuário, gráfico interativo, balanço anual CVM, notícias e carteira protegida por login.")
with c_hdr_dir:
    render_widget_ibov_google()
st.markdown(
    "<style>"
    "html,body,[data-testid='stApp'],[data-testid='stAppViewContainer']{"
    "overflow:hidden!important;height:100%!important;max-height:100vh!important;max-height:100dvh!important;}"
    "[data-testid='stMain'],section.main{"
    "overflow-y:auto!important;overflow-x:hidden!important;height:100%!important;max-height:100%!important;"
    "min-height:0!important;overflow-anchor:none!important;overscroll-behavior-y:contain;}"
    "[data-testid='stMainBlockContainer']{"
    "overflow:visible!important;height:auto!important;max-height:none!important;}"
    "div[data-testid='stExpander']{margin-bottom:10px;border-radius:8px;}"
    "</style>",
    unsafe_allow_html=True,
)

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
    with st.container(border=True):
        st.caption("📚 **Dúvida sobre alguma sigla?**")
        if st.button("📖 Dicionário de Termos", key="btn_dic_sidebar", type="primary", use_container_width=True):
            modal_dicionario()

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
    listas_url = st.query_params.get_all("listas")
    if not listas_url and setor_url in opcoes_listas:
        listas_url = [setor_url]
    default_listas = [x for x in listas_url if x in opcoes_listas]

    setores_url = st.query_params.get_all("setores")
    if not setores_url and SETOR_ALIAS.get(setor_url, setor_url) in opcoes_setores_exibir:
        setores_url = [SETOR_ALIAS.get(setor_url, setor_url)]
    default_setores = [
        SETOR_ALIAS.get(x, x) for x in setores_url if SETOR_ALIAS.get(x, x) in opcoes_setores_exibir
    ]

    if "sb_filtro_listas" not in st.session_state:
        st.session_state["sb_filtro_listas"] = default_listas
    if "sb_filtro_setores" not in st.session_state:
        st.session_state["sb_filtro_setores"] = default_setores

    filtro_listas = st.multiselect(
        "Listas rápidas:",
        options=opcoes_listas,
        key="sb_filtro_listas",
        placeholder="Todas (ou escolha 1 ou mais)",
        help="Favoritos e Carteira filtram seus ativos (interseção entre si). BESST soma-se aos Setores específicos abaixo.",
    )
    filtro_setores = st.multiselect(
        "Setores específicos:",
        options=opcoes_setores_exibir,
        key="sb_filtro_setores",
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
    if "sb_liq_label" not in st.session_state or st.session_state["sb_liq_label"] not in liq_keys:
        st.session_state["sb_liq_label"] = liq_keys[idx_liq]
    liq_label = st.selectbox("Liquidez mínima (2 meses):", liq_keys, key="sb_liq_label")
    liq_min = liq_min_opcoes[liq_label]

    if "sb_busca_tickers" not in st.session_state:
        st.session_state["sb_busca_tickers"] = st.query_params.get("busca", "")
    busca_tickers = st.text_input(
        "Filtrar códigos na barra (opcional):",
        key="sb_busca_tickers",
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
            "position:fixed!important;left:-9999px!important;top:0!important;"
            "width:1px!important;height:1px!important;opacity:0!important;"
            "pointer-events:none!important;overflow:hidden!important;margin:0!important;padding:0!important;}"
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
if filtro_listas:
    st.query_params["listas"] = filtro_listas
elif "listas" in st.query_params:
    del st.query_params["listas"]
if filtro_setores:
    st.query_params["setores"] = filtro_setores
elif "setores" in st.query_params:
    del st.query_params["setores"]
if busca_tickers.strip():
    st.query_params["busca"] = busca_tickers.strip()
elif "busca" in st.query_params:
    del st.query_params["busca"]

posicoes_carteira = consolidar_carteira_por_ativo(st.session_state["lancamentos"]) if usuario_atual else {}

mapa_setores_ativos: dict[str, str] = {}
try:
    mapa_setores_ativos.update(carregar_mapa_todos_setores())
except Exception:
    pass

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

with st.spinner(f"Buscando dados de 6 anos, indicadores fundamentalistas, técnicos e notícias para {len(tickers_para_yf)} ativos..."):
    dados_yf = buscar_yahoo_lote(tuple(tickers_para_yf))
    dados_news = buscar_sentimento_noticias_lote(tuple(tickers_para_yf))
    dados_i10 = buscar_investidor10_lote(tuple(tickers_para_yf))

nomes_cvm_mapa = carregar_nomes_cvm_tickers()
falt_meta_fund = [
    tk_m for tk_m in tickers_para_yf
    if not mapa_setores_ativos.get(tk_m) or (not nomes_cvm_mapa.get(tk_m) and (not dados_yf.get(tk_m, {}).get("nome") or dados_yf.get(tk_m, {}).get("nome") == tk_m))
]
mapa_nomes_fund_extra: dict[str, str] = {}
if 0 < len(falt_meta_fund) <= 40:
    def _fetch_meta_fund(tk_m: str):
        det_m = buscar_detalhes_fundamentus(tk_m)
        emp_m = formatar_nome_empresa_completo(det_m.get("Empresa", ""))
        set_m = " ".join((det_m.get("Setor") or "").split())
        return tk_m, emp_m, set_m

    with ThreadPoolExecutor(max_workers=6) as ex_m:
        for tk_m, emp_m, set_m in ex_m.map(_fetch_meta_fund, falt_meta_fund):
            if emp_m:
                mapa_nomes_fund_extra[tk_m] = emp_m
            if set_m and not mapa_setores_ativos.get(tk_m):
                mapa_setores_ativos[tk_m] = set_m

def montar_item_completo(a: dict) -> dict:
    t = a["ticker"]
    yf_info = dados_yf.get(t, {})
    news_info = dados_news.get(t, {})
    i10_info = dados_i10.get(t, {})
    cot = yf_info.get("cotacao_yf") or i10_info.get("cotacao_i10") or a.get("cotacao") or 0.0
    nome_yf = yf_info.get("nome")
    nome_cvm = nomes_cvm_mapa.get(t)
    nome_fd = mapa_nomes_fund_extra.get(t)
    if nome_cvm and (not nome_yf or nome_yf == t or len(nome_cvm) > len(nome_yf)):
        nome = nome_cvm
    elif nome_yf and nome_yf != t:
        nome = nome_yf
    elif nome_fd:
        nome = nome_fd
    elif nome_cvm:
        nome = nome_cvm
    else:
        nome = t

    cot_i10 = i10_info.get("cotacao_i10")
    pl_i10 = i10_info.get("pl_i10")
    pvp_i10 = i10_info.get("pvp_i10")
    lpa_i10 = i10_info.get("lpa_i10")
    vpa_i10 = i10_info.get("vpa_i10")
    roe_i10 = i10_info.get("roe_i10")
    dy_i10 = i10_info.get("dy_i10")

    lpa = lpa_i10 if lpa_i10 is not None else (a.get("lpa") if a.get("lpa") is not None else yf_info.get("lpa_yf"))
    vpa = vpa_i10 if vpa_i10 is not None else (a.get("vpa") if a.get("vpa") is not None else yf_info.get("vpa_yf"))
    roe = roe_i10 if roe_i10 is not None else (a.get("roe") if a.get("roe") is not None else yf_info.get("roe_yf"))

    if pl_i10 is not None and cot > 0 and cot_i10 and cot_i10 > 0:
        pl = pl_i10 * (cot / cot_i10)
    elif cot > 0 and lpa is not None and lpa != 0:
        pl = cot / lpa
    else:
        pl = pl_i10 if pl_i10 is not None else a.get("pl")

    if pvp_i10 is not None and cot > 0 and cot_i10 and cot_i10 > 0:
        pvp = pvp_i10 * (cot / cot_i10)
    elif cot > 0 and vpa is not None and vpa != 0:
        pvp = cot / vpa
    else:
        pvp = pvp_i10 if pvp_i10 is not None else a.get("pvp")

    dy_fund = float(a.get("dy_12m") or 0.0)
    dpa_confiavel = (cot * (dy_fund / 100.0)) if (cot > 0 and dy_fund > 0) else 0.0

    if dy_i10 is not None and dy_i10 > 0 and cot > 0 and cot_i10 and cot_i10 > 0:
        dpa_12m = float(cot_i10) * (float(dy_i10) / 100.0)
        dy_12m = (dpa_12m / cot) * 100.0
    else:
        dpa_12m_yf = yf_info.get("dpa_12m_yf")
        if dpa_12m_yf is not None and cot > 0:
            dy_yf_12m = (float(dpa_12m_yf) / cot) * 100.0
            if dy_fund > 0:
                dpa_12m = dpa_confiavel if (abs(dy_yf_12m - dy_fund) / dy_fund > 0.40) else float(dpa_12m_yf)
            else:
                dpa_12m = 0.0 if dy_yf_12m > 1.0 else float(dpa_12m_yf)
        else:
            dpa_12m = dpa_confiavel if dpa_confiavel > 0 else float(a.get("dpa_12m") or 0.0)
        dy_12m = (dpa_12m / cot) * 100.0 if (dpa_12m and cot > 0) else dy_fund

    dpa_med_6a = yf_info.get("dpa_med_6a")
    anos_hist = yf_info.get("anos_hist", 0)

    dy_ref_proj = dy_12m if dy_12m > 0 else dy_fund
    dpa_ref_proj = dpa_12m if dpa_12m > 0 else dpa_confiavel
    dpa_proj_yf = yf_info.get("dpa_proj")
    if dpa_proj_yf is not None and cot > 0:
        dy_yf_proj = (float(dpa_proj_yf) / cot) * 100.0
        if dy_ref_proj > 0:
            dpa_proj = dpa_ref_proj if (abs(dy_yf_proj - dy_ref_proj) / dy_ref_proj > 0.40) else float(dpa_proj_yf)
        else:
            dpa_proj = 0.0 if (dpa_12m == 0.0 and dy_yf_proj > 1.0) else float(dpa_proj_yf)
    else:
        dpa_proj = dpa_ref_proj if dpa_ref_proj > 0 else None

    pt_med = (dpa_med_6a / 0.06) if (dpa_med_6a and dpa_med_6a > 0) else None
    pt_proj = (dpa_proj / 0.06) if (dpa_proj and dpa_proj > 0) else None
    pt_bazin = (dpa_12m / 0.06) if (dpa_12m and dpa_12m > 0) else None
    graham = math.sqrt(22.5 * lpa * vpa) if (lpa and vpa and lpa > 0 and vpa > 0) else None

    setor_oficial_t = mapa_setores_ativos.get(t, "") or mapa_fin_seg.get(t, "")
    setor_exib_t = SETOR_CURTO.get(setor_oficial_t, setor_oficial_t)
    eh_banco_seg = (t in mapa_fin_seg) or any(
        k in _norm_txt(setor_oficial_t) for k in ("banco", "intermediarios financeiros", "seguro", "previdencia")
    )

    a_merged = dict(a)
    for k_base, k_i10 in (
        ("roic", "roic_i10"),
        ("marg_liq", "marg_liq_i10"),
        ("marg_ebit", "marg_ebit_i10"),
        ("ev_ebitda", "ev_ebitda_i10"),
        ("ev_ebit", "ev_ebit_i10"),
        ("liq_corr", "liq_corr_i10"),
        ("div_brut_patrim", "div_brut_patrim_i10"),
        ("cresc_rec_5a", "cresc_rec_5a_i10"),
    ):
        if i10_info.get(k_i10) is not None:
            a_merged[k_base] = i10_info[k_i10]

    item = {
        **a_merged,
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
        "anos_divs_consec": yf_info.get("anos_divs_consec", 0),
        "meses_dividendos": yf_info.get("meses_dividendos", []),
        "news_score": news_info.get("news_score", 0.0),
        "news_resumo": news_info.get("news_resumo", "⚪ Neutro"),
        "news_qtd_30d": news_info.get("qtd_30d", 0),
        "news_qtd_7d": news_info.get("qtd_7d", 0),
        "news_tem_rj": news_info.get("tem_rj", False),
        "top_noticia_neg": news_info.get("top_noticia_neg"),
        "top_noticia_pos": news_info.get("top_noticia_pos"),
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
            "🔵 Bom (Acúmulo LP / Desconto)",
            "🟣 Esticado (Alerta Topo/Sobrepreço)",
            "🟠 Indeciso (Sinais Mistos)",
            "🟡 Regular (Neutro / Yield Baixo)",
            "🔴 Crítico (Risco Alto)",
        ]

        if "tab1_modo_score_val" not in st.session_state:
            modo_url = st.query_params.get("modo", "")
            st.session_state["tab1_modo_score_val"] = modo_url if modo_url in MODO_SCORE_OPCOES else list(MODO_SCORE_OPCOES.keys())[0]
        if "tab1_filtro_veredito_val" not in st.session_state:
            ver_url = st.query_params.get_all("ver")
            st.session_state["tab1_filtro_veredito_val"] = [v for v in ver_url if v in VEREDITOS_OPCOES]
        if "tab1_modo_score_tab" not in st.session_state:
            st.session_state["tab1_modo_score_tab"] = st.session_state["tab1_modo_score_val"]
        if "tab1_modo_score_rank" not in st.session_state:
            st.session_state["tab1_modo_score_rank"] = st.session_state["tab1_modo_score_val"]
        if "tab1_filtro_ver_tab" not in st.session_state:
            st.session_state["tab1_filtro_ver_tab"] = list(st.session_state["tab1_filtro_veredito_val"])
        if "tab1_filtro_ver_rank" not in st.session_state:
            st.session_state["tab1_filtro_ver_rank"] = list(st.session_state["tab1_filtro_veredito_val"])

        def _sync_modo_tab():
            val = st.session_state["tab1_modo_score_tab"]
            st.session_state["tab1_modo_score_val"] = val
            st.session_state["tab1_modo_score_rank"] = val
            st.query_params["modo"] = val

        def _sync_modo_rank():
            val = st.session_state["tab1_modo_score_rank"]
            st.session_state["tab1_modo_score_val"] = val
            st.session_state["tab1_modo_score_tab"] = val
            st.query_params["modo"] = val

        def _sync_ver_tab():
            val = list(st.session_state["tab1_filtro_ver_tab"])
            st.session_state["tab1_filtro_veredito_val"] = val
            st.session_state["tab1_filtro_ver_rank"] = val
            if val:
                st.query_params["ver"] = val
            elif "ver" in st.query_params:
                del st.query_params["ver"]

        def _sync_ver_rank():
            val = list(st.session_state["tab1_filtro_ver_rank"])
            st.session_state["tab1_filtro_veredito_val"] = val
            st.session_state["tab1_filtro_ver_tab"] = val
            if val:
                st.query_params["ver"] = val
            elif "ver" in st.query_params:
                del st.query_params["ver"]

        modo_score_lbl = st.session_state["tab1_modo_score_val"]
        filtro_vereditos = st.session_state["tab1_filtro_veredito_val"]
        st.query_params["modo"] = modo_score_lbl
        if filtro_vereditos:
            st.query_params["ver"] = filtro_vereditos
        elif "ver" in st.query_params:
            del st.query_params["ver"]
        chave_score_ativo = MODO_SCORE_OPCOES.get(modo_score_lbl, "score_geral")

        resultados_tab = [
            {**r, "pos_ranking": idx_m, "score_ativo": r[chave_score_ativo]}
            for idx_m, r in enumerate(
                sorted(resultados, key=lambda x: x[chave_score_ativo], reverse=True),
                start=1,
            )
        ]
        if filtro_vereditos:
            ver_prefixos = tuple(" ".join(v.split()[:2]) for v in filtro_vereditos)
            resultados_tab = [r for r in resultados_tab if str(r.get("veredito", "")).startswith(ver_prefixos)]

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

        st.text_input(
            "comp_bridge_input",
            key="comp_bridge",
            label_visibility="collapsed",
            on_change=_ao_clicar_comparar_tabela,
        )
        st.text_input(
            "raiox_bridge_input",
            key="raiox_bridge",
            label_visibility="collapsed",
            on_change=_ao_clicar_ticker_tabela,
        )
        st.markdown(
            "<style>"
            "div[data-testid='stElementContainer']:has(input[aria-label='raiox_bridge_input']),"
            "div.element-container:has(input[aria-label='raiox_bridge_input']),"
            "div[data-testid='stElementContainer']:has(input[aria-label='comp_bridge_input']),"
            "div.element-container:has(input[aria-label='comp_bridge_input']),"
            "div[data-testid='stElementContainer']:has(iframe[height='0']),"
            "div.element-container:has(iframe[height='0']){"
            "position:fixed!important;left:-9999px!important;top:0!important;"
            "width:1px!important;height:1px!important;opacity:0!important;"
            "pointer-events:none!important;overflow:hidden!important;margin:0!important;padding:0!important;}"
            "div[data-testid='stVerticalBlock']:has(> div .raiox-table-host),"
            "div[data-testid='stVerticalBlock']:has(> div > div .raiox-table-host){gap:0!important;}"
            ".val-table-wrap{width:100%;overflow-x:auto;overflow-y:hidden;margin:0;padding:0;}"
            ".val-table-wrap-top{margin-top:12px;}"
            ".val-table-wrap-top:last-child,.val-table-wrap-bot{margin-bottom:12px;}"
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

        if len(resultados_tab) >= 2:
            with st.expander("📡 Radar de Destaques Rápidos — clique para minimizar/maximizar", expanded=True):
                rc1, rc2, rc3, rc4 = st.columns(4)

                # Card 1: Líder de Atratividade
                lider_atr = resultados_tab[0]
                with rc1:
                    with st.container(border=True):
                        st.markdown(
                            "<div style='min-height:164px; display:flex; flex-direction:column; justify-content:space-between;'>"
                            "<div>"
                            "<div style='font-size:14px; font-weight:700; margin-bottom:4px; white-space:nowrap; overflow:hidden; text-overflow:ellipsis;'>🏆 Líder de Atratividade</div>"
                            f"<div style='font-size:20px; font-weight:700; color:#60a5fa; line-height:1.2;'>{lider_atr['ticker']}</div>"
                            f"<div style='font-size:12px; opacity:0.8; white-space:nowrap; overflow:hidden; text-overflow:ellipsis;' title='{html.escape(lider_atr['nome'])}'>{html.escape(lider_atr['nome'])}</div>"
                            "</div>"
                            "<div>"
                            f"<div style='font-size:13px;'>Cotação: <strong>R$ {fmt_num(lider_atr['cotacao'])}</strong></div>"
                            f"<div style='font-size:13px;'>Score Ativo: <strong>{fmt_num(lider_atr['score_ativo'], 1)}/100</strong></div>"
                            f"<div style='margin-top:4px; min-height:22px; display:flex; align-items:center;'>{badge_veredito_html(lider_atr.get('veredito', ''))}</div>"
                            "</div>"
                            "</div>",
                            unsafe_allow_html=True,
                        )

                # Card 2: Maior DY Sustentável
                cands_dy = [
                    r for r in resultados_tab
                    if float(r.get("dy_12m") or 0.0) > 0.0
                    and not r.get("eh_value_trap")
                    and (r.get("roe") is not None and float(r["roe"]) > 10.0)
                    and (
                        (r.get("marg_liq") is not None and float(r["marg_liq"]) > 0.0)
                        or (r.get("eh_banco_seg") and (r.get("marg_liq") is None or float(r["marg_liq"]) == 0.0) and (r.get("pl") is None or float(r["pl"]) > 0.0))
                    )
                ]
                with rc2:
                    with st.container(border=True):
                        if cands_dy:
                            top_dy = max(cands_dy, key=lambda x: float(x["dy_12m"]))
                            bz_dy = top_dy.get("pt_bazin")
                            bz_txt = f"R$ {fmt_num(bz_dy)}" if (bz_dy and bz_dy > 0) else "—"
                            st.markdown(
                                "<div style='min-height:164px; display:flex; flex-direction:column; justify-content:space-between;'>"
                                "<div>"
                                "<div style='font-size:14px; font-weight:700; margin-bottom:4px; white-space:nowrap; overflow:hidden; text-overflow:ellipsis;'>💰 Maior DY Sustentável</div>"
                                f"<div style='font-size:20px; font-weight:700; color:#22c55e; line-height:1.2;'>{top_dy['ticker']}</div>"
                                f"<div style='font-size:12px; opacity:0.8; white-space:nowrap; overflow:hidden; text-overflow:ellipsis;' title='{html.escape(top_dy['nome'])}'>{html.escape(top_dy['nome'])}</div>"
                                "</div>"
                                "<div>"
                                f"<div style='font-size:13px;'>Cotação: <strong>R$ {fmt_num(top_dy['cotacao'])}</strong></div>"
                                f"<div style='font-size:13px;'>DY 12m: <strong>{fmt_num(top_dy['dy_12m'], 2)}%</strong></div>"
                                f"<div style='font-size:12px; opacity:0.85; min-height:22px; display:flex; align-items:center;'>Teto Bazin:&nbsp;<strong>{bz_txt}</strong></div>"
                                "</div>"
                                "</div>",
                                unsafe_allow_html=True,
                            )
                        else:
                            st.markdown(
                                "<div style='min-height:164px; display:flex; flex-direction:column; justify-content:space-between;'>"
                                "<div style='font-size:14px; font-weight:700;'>💰 Maior DY Sustentável</div>"
                                "<div style='font-size:12px; opacity:0.75;'>Sem ativo elegível com ROE &gt; 10% e DY &gt; 0% neste filtro.</div>"
                                "<div></div>"
                                "</div>",
                                unsafe_allow_html=True,
                            )

                # Card 3: Oportunidade Técnica (Sobrevendida)
                cands_ifr = [
                    r for r in resultados_tab
                    if r.get("ifr_14") is not None
                    and not r.get("eh_value_trap")
                    and (r.get("roe") is not None and float(r["roe"]) > 0.0)
                    and (r.get("pl") is None or float(r["pl"]) > 0.0)
                    and float(r.get("score_lp") or 0.0) >= 50.0
                ]
                if not cands_ifr:
                    cands_ifr = [
                        r for r in resultados_tab
                        if r.get("ifr_14") is not None
                        and not r.get("eh_value_trap")
                        and (r.get("roe") is None or float(r["roe"]) > 0.0)
                    ]
                with rc3:
                    with st.container(border=True):
                        if cands_ifr:
                            top_ifr = min(cands_ifr, key=lambda x: float(x["ifr_14"]))
                            d200_i = top_ifr.get("dist_mm200_pct")
                            d200_s = f"{d200_i:+.1f}%" if d200_i is not None else "—"
                            st.markdown(
                                "<div style='min-height:164px; display:flex; flex-direction:column; justify-content:space-between;'>"
                                "<div>"
                                "<div style='font-size:14px; font-weight:700; margin-bottom:4px; white-space:nowrap; overflow:hidden; text-overflow:ellipsis;'>⚡ Oportunidade Técnica</div>"
                                f"<div style='font-size:20px; font-weight:700; color:#facc15; line-height:1.2;'>{top_ifr['ticker']}</div>"
                                f"<div style='font-size:12px; opacity:0.8; white-space:nowrap; overflow:hidden; text-overflow:ellipsis;' title='{html.escape(top_ifr['nome'])}'>{html.escape(top_ifr['nome'])}</div>"
                                "</div>"
                                "<div>"
                                f"<div style='font-size:13px;'>Cotação: <strong>R$ {fmt_num(top_ifr['cotacao'])}</strong></div>"
                                f"<div style='font-size:13px;'>IFR (14d): <strong>{fmt_num(top_ifr['ifr_14'], 1)}</strong></div>"
                                f"<div style='font-size:12px; opacity:0.85; min-height:22px; display:flex; align-items:center;'>Dist. MM200:&nbsp;<strong>{d200_s}</strong></div>"
                                "</div>"
                                "</div>",
                                unsafe_allow_html=True,
                            )
                        else:
                            st.markdown(
                                "<div style='min-height:164px; display:flex; flex-direction:column; justify-content:space-between;'>"
                                "<div style='font-size:14px; font-weight:700;'>⚡ Oportunidade Técnica</div>"
                                "<div style='font-size:12px; opacity:0.75;'>Indicadores técnicos não carregados para este filtro.</div>"
                                "<div></div>"
                                "</div>",
                                unsafe_allow_html=True,
                            )

                # Card 4: Maior Desconto Graham
                cands_gr = []
                for r_g in resultados_tab:
                    if r_g.get("eh_value_trap"):
                        continue
                    ms_g = calc_ms(r_g.get("graham"), r_g["cotacao"])
                    if ms_g is not None and ms_g > 0.0:
                        cands_gr.append((ms_g, r_g))
                with rc4:
                    with st.container(border=True):
                        if cands_gr:
                            ms_best, top_gr = max(cands_gr, key=lambda pair: pair[0])
                            st.markdown(
                                "<div style='min-height:164px; display:flex; flex-direction:column; justify-content:space-between;'>"
                                "<div>"
                                "<div style='font-size:14px; font-weight:700; margin-bottom:4px; white-space:nowrap; overflow:hidden; text-overflow:ellipsis;'>🛡️ Maior Desconto Graham</div>"
                                f"<div style='font-size:20px; font-weight:700; color:#38bdf8; line-height:1.2;'>{top_gr['ticker']}</div>"
                                f"<div style='font-size:12px; opacity:0.8; white-space:nowrap; overflow:hidden; text-overflow:ellipsis;' title='{html.escape(top_gr['nome'])}'>{html.escape(top_gr['nome'])}</div>"
                                "</div>"
                                "<div>"
                                f"<div style='font-size:13px;'>Cotação: <strong>R$ {fmt_num(top_gr['cotacao'])}</strong></div>"
                                f"<div style='font-size:13px;'>Graham: <strong>R$ {fmt_num(top_gr['graham'])}</strong></div>"
                                f"<div style='font-size:12px; color:#22c55e; font-weight:700; min-height:22px; display:flex; align-items:center;'>Margem: +{fmt_num(ms_best, 1)}%</div>"
                                "</div>"
                                "</div>",
                                unsafe_allow_html=True,
                            )
                        else:
                            st.markdown(
                                "<div style='min-height:164px; display:flex; flex-direction:column; justify-content:space-between;'>"
                                "<div style='font-size:14px; font-weight:700;'>🛡️ Maior Desconto Graham</div>"
                                "<div style='font-size:12px; opacity:0.75;'>Nenhum ativo abaixo do valor de Graham neste filtro.</div>"
                                "<div></div>"
                                "</div>",
                                unsafe_allow_html=True,
                            )
            st.markdown("<div style='height:8px;'></div>", unsafe_allow_html=True)

        with st.expander(f"📋 Tabela Comparativa ({len(resultados_tab)} ativos no filtro) — clique para minimizar/maximizar | clique em qualquer linha para abrir/fechar o Raio-X", expanded=True):
            with st.container(border=True):
                c_modo_sc, c_filt_ver, c_dic_tab = st.columns([2.0, 1.35, 0.9], vertical_alignment="bottom")
                with c_modo_sc:
                    st.radio(
                        "🎯 Modo de Análise / Score:",
                        options=list(MODO_SCORE_OPCOES.keys()),
                        horizontal=True,
                        key="tab1_modo_score_tab",
                        on_change=_sync_modo_tab,
                    )
                with c_filt_ver:
                    st.multiselect(
                        "🏷️ Filtrar por Veredito do Modelo:",
                        options=VEREDITOS_OPCOES,
                        placeholder="Todos os vereditos (ex: 🟢 Excelente, 🔵 Bom)",
                        key="tab1_filtro_ver_tab",
                        on_change=_sync_ver_tab,
                    )
                with c_dic_tab:
                    if st.button("📖 Dicionário de Termos", key="btn_dic_tab1", use_container_width=True):
                        modal_dicionario()

            c_busca, c_ord1, c_ord2, c_ord3 = st.columns([1.8, 1.8, 1.4, 1.2], vertical_alignment="bottom")
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
            ord_keys = list(opcoes_ordenacao.keys())
            if "tab1_ord_col" not in st.session_state or st.session_state["tab1_ord_col"] not in ord_keys:
                ord_url = st.query_params.get("ord", "")
                st.session_state["tab1_ord_col"] = ord_url if ord_url in ord_keys else ord_keys[0]
            dir_opcoes = ["Decrescente (Maior → Menor)", "Crescente (Menor → Maior)"]
            if "tab1_ord_dir" not in st.session_state or st.session_state["tab1_ord_dir"] not in dir_opcoes:
                dir_url = st.query_params.get("dir", "")
                if dir_url in dir_opcoes:
                    st.session_state["tab1_ord_dir"] = dir_url
                else:
                    st.session_state["tab1_ord_dir"] = dir_opcoes[1 if st.session_state["tab1_ord_col"] in ("P/L", "P/VP", "Ticker (A-Z)") else 0]
            if "tab1_max_linhas" not in st.session_state:
                try:
                    maxl_url = int(st.query_params.get("maxl", "50"))
                    st.session_state["tab1_max_linhas"] = max(0, min(1000, maxl_url))
                except Exception:
                    st.session_state["tab1_max_linhas"] = 50

            with c_busca:
                q_url = st.query_params.get("q", "")
                if "value" in inspect.signature(st_keyup).parameters:
                    busca_tabela = st_keyup("🔎 Buscar na tabela (ao digitar):", value=q_url, placeholder="Ex: PETR, BBAS, CEMIG", debounce=200, key="busca_live")
                else:
                    busca_tabela = st_keyup("🔎 Buscar na tabela (ao digitar):", placeholder="Ex: PETR, BBAS, CEMIG", debounce=200, key="busca_live")
            with c_ord1:
                col_escolhida = st.selectbox("Ordenar por coluna:", ord_keys, key="tab1_ord_col")
            with c_ord2:
                direcao = st.selectbox("Ordem:", dir_opcoes, key="tab1_ord_dir")
            with c_ord3:
                max_linhas = st.number_input("Exibir (0 = todos):", min_value=0, max_value=1000, step=10, key="tab1_max_linhas")

            st.query_params["ord"] = col_escolhida
            st.query_params["dir"] = direcao
            st.query_params["maxl"] = str(int(max_linhas))
            if busca_tabela and busca_tabela.strip():
                st.query_params["q"] = busca_tabela.strip()
            elif "q" in st.query_params:
                del st.query_params["q"]

            lista_tab = resultados_tab
            if busca_tabela and busca_tabela.strip():
                termo = busca_tabela.strip().upper()
                lista_tab = [r for r in resultados_tab if termo in r["ticker"] or termo in r["nome"].upper()]

            chave_ord = opcoes_ordenacao[col_escolhida]
            reverso = direcao.startswith("Decrescente")
            resultados_ordenados = sort_resultados(lista_tab, chave_ord, reverso)
            exibir = resultados_ordenados if max_linhas == 0 else resultados_ordenados[:int(max_linhas)]

            falt_i10_tab = tuple(r["ticker"] for r in exibir if r["ticker"] not in dados_i10)
            mapa_res_tab = {r["ticker"]: r for r in resultados_tab}
            if falt_i10_tab and len(falt_i10_tab) <= 60:
                if len(falt_i10_tab) <= 15:
                    falt_yf_t = tuple(tk for tk in falt_i10_tab if tk not in dados_yf)
                    if falt_yf_t:
                        dados_yf.update(buscar_yahoo_lote(falt_yf_t))
                    falt_nw_t = tuple(tk for tk in falt_i10_tab if tk not in dados_news)
                    if falt_nw_t:
                        dados_news.update(buscar_sentimento_noticias_lote(falt_nw_t))
                dados_i10.update(buscar_investidor10_lote(falt_i10_tab))
                mapa_base_todos = {a["ticker"]: a for a in todos_ativos}
                exibir_upd = []
                for r_ex in exibir:
                    tk_ex = r_ex["ticker"]
                    if tk_ex in falt_i10_tab and tk_ex in mapa_base_todos:
                        it_upd = montar_item_completo(mapa_base_todos[tk_ex])
                        it_upd["pos_ranking"] = r_ex["pos_ranking"]
                        it_upd["score_ativo"] = it_upd[chave_score_ativo]
                        exibir_upd.append(it_upd)
                        mapa_res_tab[tk_ex] = it_upd
                    else:
                        exibir_upd.append(r_ex)
                exibir = exibir_upd

            st.caption(f"Mostrando **{len(exibir)}** de **{len(lista_tab)}** ativos.")

            if not exibir:
                st.warning("Nenhum ativo corresponde à busca digitada na tabela.")
            else:
                comp_set = set(st.session_state.get("comp_selecionados", []))
                if comp_set:
                    c_info_cmp, c_btn_cmp = st.columns([4, 1], vertical_alignment="center")
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

                @st.fragment
                def render_tabela_e_raiox(exibir_rows: list[dict], opcoes_rx: list[str], mapa_res: dict[str, dict], comp_ativos: set[str], modo_score_chave: str = "score_geral"):
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
                            f"<span style='font-weight:700;' title='Posição no Ranking e Score Ativo (0 a 100)'>{r['pos_ranking']}º · <strong>{fmt_num(score_at, 1)}</strong></span>"
                            f"<br>{badge_v}"
                            f"<br><small style='opacity:0.85; white-space:nowrap;' title='IFR 14 dias (RSI): {ifr_ic} | Notícias 30d: {html.escape(news_res_r)}'>{ifr_ic} | {news_ic}</small>"
                            f"</td>"
                            f"<td><span style='color:#60a5fa; font-weight:700;'>{r['ticker']}</span>{estrela}<br><small style='opacity:0.88;'>{nome_esc}</small>{setor_badge}</td>"
                            f"<td><strong>R$ {fmt_num(cot)}</strong><br><small title='Dividend Yield (12 meses): percentual pago em dividendos/JCP sobre a cotação atual'>DY: {fmt_num(r['dy_12m'])}%</small></td>"
                            f"<td><span title='Preço sobre Lucro: anos para reaver o investimento via lucro'>P/L:</span> {pl_txt}<br><span title='Preço sobre Valor Patrimonial: abaixo de 1,0 indica desconto contábil'>P/VP:</span> {pvp_html}<br><span title='Retorno sobre Patrimônio Líquido: eficiência na geração de lucro'>ROE:</span> {roe_txt}</td>"
                            f"<td><span title='Lucro por Ação (12m)'>LPA:</span> {lpa_txt} | <span title='Valor Patrimonial por Ação'>VPA:</span> {vpa_txt}<br><span title='Dividendo por Ação pago nos últimos 12 meses e média anual de 6 anos'>12m: R$ {fmt_num(r['dpa_12m'])} | 6a: {dpa6_txt}</span><br><span title='Dividendo por Ação projetado'>Proj: {dpap_txt}</span></td>"
                            f"<td>{html_preco_ms(r['pt_med'], cot, sufixo_6a)}</td>"
                            f"<td>{html_preco_ms(r['pt_proj'], cot)}</td>"
                            f"<td>{html_preco_ms(r['pt_bazin'], cot)}</td>"
                            f"<td>{html_preco_ms(r['graham'], cot)}</td>"
                            "</tr>"
                        )
                        linhas_html.append(linha)

                    thead_html = (
                        "<thead><tr>"
                        "<th style='text-align:center;' title='Marque os ativos para comparar lado a lado na aba Comparar Ativos'>⚖️</th>"
                        "<th style='text-align:center;' title='Posição no Ranking, Score Ativo (0 a 100), Veredito do Modelo, IFR 14 dias e Sentimento de Notícias (30d)'>Rank / Score<br><small>Veredito | IFR | News</small></th>"
                        "<th title='Código na B3, nome da empresa e setor de atuação'>Ticker / Empresa</th>"
                        f"<th title='Cotação atual da ação e DY (Dividend Yield): percentual pago em dividendos nos últimos 12 meses'>Cotação ({datetime.now(BRT).strftime('%d/%m/%Y %H:%M')}) & DY</th>"
                        "<th title='P/L: Preço/Lucro | P/VP: Preço/Valor Patrimonial | ROE: Retorno sobre Patrimônio Líquido'>Indicadores<br><small>(P/L | P/VP | ROE)</small></th>"
                        "<th title='LPA: Lucro por Ação | VPA: Valor Patrimonial por Ação | DPA: Dividendo por Ação (12m, média 6 anos e projetivo)'>Dados Base<br><small>(LPA | VPA | DPAs)</small></th>"
                        "<th title='Preço-Teto Médio (6a): teto para 6% de yield usando a média de dividendos de 6 anos | MS: Margem de Segurança'>Preço Teto Médio (6a) & MS</th>"
                        "<th title='Preço-Teto Projetivo: teto para 6% de yield considerando o dividendo projetado | MS: Margem de Segurança'>Preço Teto Projetivo & MS</th>"
                        "<th title='Preço-Teto Bazin (12m): DPA dos últimos 12 meses dividido por 6% (método Décio Bazin) | MS: Margem de Segurança'>Preço-Teto Bazin (12m) & MS</th>"
                        "<th title='Preço Justo de Graham: valor intrínseco pela fórmula √(22,5 × LPA × VPA) | MS: Margem de Segurança'>Preço Justo Graham & MS</th>"
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
                                c_rx1, c_rx2 = st.columns([3.8, 1], vertical_alignment="bottom")
                                with c_rx1:
                                    st.selectbox(
                                        "🔎 Raio-X do Ativo selecionado:",
                                        options=opcoes_rx,
                                        key="raiox_ativo_sel",
                                    )
                                with c_rx2:
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
                    mapa_res_tab,
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
                if (!vaiFechar) {
                    setTimeout(function() {
                        if (pWin.__raioxPendingScroll === ticker) {
                            pWin.__raioxPendingScroll = null;
                        }
                    }, 3000);
                }
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
                if (!topTable || topTable.offsetParent === null) return;
                const rectTop = topTable.getBoundingClientRect();
                if (!rectTop || rectTop.width === 0 || rectTop.height === 0) return;
                const botTable = pDoc.querySelector("table.val-table-bot");
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
                let resizeTimer = null;
                pWin.__valTableObserver = new MutationObserver(function() {
                    if (resizeTimer) {
                        clearTimeout(resizeTimer);
                    }
                    resizeTimer = setTimeout(function() {
                        resizeTimer = null;
                        pWin.requestAnimationFrame(function() {
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
                    }, 60);
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
            with st.container(border=True):
                if total_rank > 1:
                    c_r_modo, c_r_ver, c_r_qtd = st.columns([2.1, 1.5, 1.1])
                else:
                    c_r_modo, c_r_ver = st.columns([2.2, 1.5])
                with c_r_modo:
                    st.radio(
                        "🎯 Modo de Análise / Score:",
                        options=list(MODO_SCORE_OPCOES.keys()),
                        horizontal=True,
                        key="tab1_modo_score_rank",
                        on_change=_sync_modo_rank,
                    )
                with c_r_ver:
                    st.multiselect(
                        "🏷️ Filtrar por Veredito do Modelo:",
                        options=VEREDITOS_OPCOES,
                        placeholder="Todos os vereditos (ex: 🟢 Excelente, 🔵 Bom)",
                        key="tab1_filtro_ver_rank",
                        on_change=_sync_ver_rank,
                    )
                if total_rank > 1:
                    if "qtd_ranking_input" in st.session_state and st.session_state["qtd_ranking_input"] > total_rank:
                        st.session_state["qtd_ranking_input"] = total_rank
                    with c_r_qtd:
                        qtd_ranking = st.number_input(
                            f"Mostrar no Ranking (1 a {total_rank}):",
                            min_value=1,
                            max_value=total_rank,
                            value=min(100, total_rank),
                            step=10,
                            key="qtd_ranking_input",
                        )
                else:
                    qtd_ranking = total_rank

                opcoes_rank_busca = []
                mapa_lbl_para_tk_rank = {}
                for r_op in lista_rank_base:
                    lbl_rk = f"{r_op['ticker']} — {r_op['nome']}" if (r_op.get("nome") and r_op["nome"] != r_op["ticker"]) else r_op["ticker"]
                    opcoes_rank_busca.append(lbl_rk)
                    mapa_lbl_para_tk_rank[lbl_rk] = r_op["ticker"]

                if "rank_filtro_ativos_esp" in st.session_state:
                    set_opc_rk = set(opcoes_rank_busca)
                    st.session_state["rank_filtro_ativos_esp"] = [
                        x for x in st.session_state["rank_filtro_ativos_esp"] if x in set_opc_rk
                    ]

                sel_rank_esp = st.multiselect(
                    "🔎 Filtrar / Comparar ativos específicos no Ranking (sigla ou nome):",
                    options=opcoes_rank_busca,
                    placeholder="Digite sigla ou nome (ex: PETR4, Petrobras, TAEE11, Taesa) — vazio mostra os Top N",
                    key="rank_filtro_ativos_esp",
                )

            if total_rank == 0:
                st.info("Nenhum ativo corresponde aos filtros de Veredito ou busca selecionados.")
            else:
                if sel_rank_esp:
                    tks_sel_rk = {mapa_lbl_para_tk_rank[lbl] for lbl in sel_rank_esp if lbl in mapa_lbl_para_tk_rank}
                    itens_exibir_rank = [r for r in lista_rank_base if r["ticker"] in tks_sel_rk]
                else:
                    itens_exibir_rank = lista_rank_base[:int(qtd_ranking)]

                for r in itens_exibir_rank:
                    score_at = r.get("score_ativo", r.get(chave_score_ativo, r["score_geral"]))
                    news_sc = float(r.get("news_score") or 0.0)
                    news_res = r.get("news_resumo", "⚪ Neutro")
                    justificativa = gerar_justificativa_detalhada(r, chave_score_ativo)
                    estrela = " ⭐" if r["ticker"] in st.session_state["favoritos"] else ""
                    with st.container(border=True):
                        st.markdown(
                            "<div style='display:flex; flex-wrap:wrap; justify-content:space-between; align-items:center; gap:8px; margin-bottom:6px;'>"
                            "<div style='font-size:16px; font-weight:700;'>"
                            f"{r['pos_ranking']}º Lugar: <span style='color:#60a5fa;'>{r['ticker']}{estrela}</span> "
                            f"<span style='font-size:13px; font-weight:500; opacity:0.85;'>({html.escape(r['nome'])})</span>"
                            "</div>"
                            "<div style='display:flex; flex-wrap:wrap; align-items:center; gap:10px; font-size:14px;'>"
                            f"<span>Cotação: <strong>R$ {fmt_num(r['cotacao'])}</strong></span>"
                            f"<span>Score Ativo: <strong>{score_at}/100</strong></span>"
                            f"{badge_veredito_html(r.get('veredito', ''))}"
                            "</div>"
                            "</div>"
                            "<div style='font-size:13px; opacity:0.9; margin-bottom:4px;'>"
                            f"📊 LP: <strong>{r['score_lp']}</strong> &nbsp;|&nbsp; "
                            f"CP: <strong>{r['score_cp']}</strong> &nbsp;|&nbsp; "
                            f"News: <strong>{news_sc:+.1f}</strong> ({html.escape(news_res)})"
                            "</div>",
                            unsafe_allow_html=True,
                        )
                        st.markdown(fmt_faixa_preco_html(r), unsafe_allow_html=True)
                        partes_just_rk = justificativa.split("\n\n", 1)
                        with st.container(border=True):
                            st.markdown(partes_just_rk[0])
                            if len(partes_just_rk) > 1 and partes_just_rk[1].strip():
                                st.markdown(
                                    "<div style='margin:8px 0 6px 0; border-top:1px solid rgba(128,128,128,0.20);'></div>",
                                    unsafe_allow_html=True,
                                )
                                st.markdown(partes_just_rk[1], unsafe_allow_html=True)

        # --- SETOR DE ÚLTIMAS NOTÍCIAS E FATOS RELEVANTES (ABAIXO DO RANKING) ---
        ativos_para_news = exibir if exibir else lista_rank_base
        with st.expander("📰 Últimas Informações e Notícias dos Ativos Pesquisados / Filtrados — clique para minimizar/maximizar", expanded=True):
            if not ativos_para_news:
                st.info("Nenhum ativo no filtro atual para exibir notícias.")
            else:
                opcoes_news_lbl = []
                mapa_news_lbl_para_tk = {}
                for r_nw in ativos_para_news:
                    lbl_nw = f"{r_nw['ticker']} — {r_nw['nome']}" if (r_nw.get("nome") and r_nw["nome"] != r_nw["ticker"]) else r_nw["ticker"]
                    opcoes_news_lbl.append(lbl_nw)
                    mapa_news_lbl_para_tk[lbl_nw] = r_nw["ticker"]

                if "ms_news_sel" in st.session_state:
                    set_opc_nw = set(opcoes_news_lbl)
                    st.session_state["ms_news_sel"] = [
                        x for x in st.session_state["ms_news_sel"] if x in set_opc_nw
                    ]

                limite_news = min(50, len(ativos_para_news))
                if limite_news > 1:
                    if st.session_state.get("_last_limite_news") != limite_news:
                        st.session_state["qtd_news_input"] = limite_news
                        st.session_state["_last_limite_news"] = limite_news
                    c_nw1, c_nw2 = st.columns([1.4, 2.6], vertical_alignment="bottom")
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
                        tks_news_sel = st.multiselect(
                            "Ou escolha ativos específicos da lista atual (sigla ou nome):",
                            options=opcoes_news_lbl,
                            placeholder="Digite sigla ou nome (ex: BBAS3, Banco do Brasil, CMIG, Cemig)",
                            key="ms_news_sel",
                        )
                    alvo_news = (
                        [mapa_news_lbl_para_tk[x] for x in tks_news_sel if x in mapa_news_lbl_para_tk]
                        if tks_news_sel
                        else [r["ticker"] for r in ativos_para_news[:int(qtd_news)]]
                    )
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
        faltantes_i10 = tuple(t for t in selecionados if t not in dados_i10)
        if faltantes_i10:
            dados_i10.update(buscar_investidor10_lote(faltantes_i10))

        itens_comp = []
        for t in selecionados:
            if t in mapa_res and t not in extra_yf and t not in faltantes_nw and t not in faltantes_i10:
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
                    st.markdown(
                        f"<h3 style='margin:0 0 2px 0;'>{r['ticker']} ({r['pos_ranking']}º)</h3>"
                        f"<div style='font-size:12.5px; opacity:0.75; white-space:nowrap; overflow:hidden; text-overflow:ellipsis; margin-bottom:8px;' "
                        f"title='{html.escape(r['nome'])}'>{html.escape(r['nome'])}</div>",
                        unsafe_allow_html=True,
                    )
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
        cp1, cp2 = st.columns([3, 1.2], vertical_alignment="bottom")
        with cp1:
            per_comp = st.radio("Período da comparação:", ["30 D", "6 M", "YTD", "1 A", "5 A", "10 A"], index=3, horizontal=True, key="comp_per")
        with cp2:
            tipo_comp = st.selectbox("Tipo:", ["Cotação ajustada", "Cotação simples"], index=0, key="comp_tipo")

        fig_comp = go.Figure()
        for r in itens_comp:
            s = buscar_historico_preco(r["ticker"], per_comp, tipo_comp == "Cotação ajustada", cot_live=r.get("cotacao"))
            if not s.empty and float(s.iloc[0]) > 0:
                pct = ((s / float(s.iloc[0])) - 1.0) * 100
                fig_comp.add_trace(
                    go.Scatter(
                        x=pct.index, y=pct.values, mode="lines", name=f"{r['ticker']} ({pct.iloc[-1]:+.1f}%)",
                        hovertemplate=f"<b>{r['ticker']}</b><br>%{{x|%d/%m/%Y}}: %{{y:+.2f}}%<extra></extra>",
                    )
                )
        fig_comp.update_layout(
            height=355, margin=dict(l=10, r=60, t=36, b=24),
            paper_bgcolor="rgba(0,0,0,0)", plot_bgcolor="rgba(0,0,0,0)",
            hovermode="x unified",
            dragmode="pan",
            yaxis=dict(
                side="right", showgrid=True, gridcolor="rgba(128,128,128,0.25)", ticksuffix="%",
                showspikes=True, spikemode="across", spikesnap="cursor", spikethickness=1,
                spikecolor="rgba(148,163,184,0.55)", spikedash="dash",
            ),
            xaxis=dict(
                showgrid=True, gridcolor="rgba(128,128,128,0.12)",
                showspikes=True, spikemode="across", spikesnap="cursor", spikethickness=1,
                spikecolor="rgba(148,163,184,0.55)", spikedash="dash",
            ),
            legend=dict(orientation="h", yanchor="bottom", y=1.02, xanchor="left", x=0),
        )
        st.plotly_chart(
            fig_comp,
            use_container_width=True,
            config={"scrollZoom": True, "displaylogo": False, "modeBarButtonsToRemove": ["zoom2d", "zoomIn2d", "zoomOut2d", "lasso2d", "select2d"]},
        )
        st.caption("💡 DEXTools: Segure **Shift + Botão Esquerdo e arraste** (ou clique em **📏 Medir**) para medir a variação (%) · Role o mouse para zoom · Arraste para mover.")

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
        c_head, c_btn_top = st.columns([3.5, 1.3], vertical_alignment="center")
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
            faltantes_ci = tuple(t for t in tickers_cart if t not in dados_i10)
            if faltantes_ci:
                dados_i10.update(buscar_investidor10_lote(faltantes_ci))

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
                    st.markdown(
                        "<div style='min-height:92px; display:flex; flex-direction:column; justify-content:space-between;'>"
                        "<div style='font-size:13px; opacity:0.78;'>💼 Patrimônio total</div>"
                        f"<div style='line-height:1.25;'><span style='font-size:23px; font-weight:700;'>R$ {fmt_num(total_atual)}</span> <span style='color:{cor_v}; font-weight:600;'>{var_cart_pct:+.2f}%</span></div>"
                        f"<div style='font-size:12.5px; opacity:0.82;'>Valor investido: <strong>R$ {fmt_num(total_investido)}</strong></div>"
                        "</div>",
                        unsafe_allow_html=True,
                    )
            with k2:
                with st.container(border=True):
                    cor_l = "#22c55e" if lucro_total >= 0 else "#ef4444"
                    st.markdown(
                        "<div style='min-height:92px; display:flex; flex-direction:column; justify-content:space-between;'>"
                        "<div style='font-size:13px; opacity:0.78;'>💰 Lucro total</div>"
                        f"<div style='font-size:23px; font-weight:700; color:{cor_l}; line-height:1.25;'>R$ {fmt_num(lucro_total)}</div>"
                        f"<div style='font-size:12.5px; opacity:0.82;'>Ganho Cap: <strong>R$ {fmt_num(ganho_cap_tot)}</strong> | Divs: <strong>R$ {fmt_num(divs_total_recebidos)}</strong></div>"
                        "</div>",
                        unsafe_allow_html=True,
                    )
            with k3:
                with st.container(border=True):
                    st.markdown(
                        "<div style='min-height:92px; display:flex; flex-direction:column; justify-content:space-between;'>"
                        "<div style='font-size:13px; opacity:0.78;'>💵 Proventos Recebidos (12M)</div>"
                        f"<div style='font-size:23px; font-weight:700; line-height:1.25;'>R$ {fmt_num(divs_12m_recebidos)}</div>"
                        f"<div style='font-size:12.5px; opacity:0.82;'>Total recebido desde compras: <strong>R$ {fmt_num(divs_total_recebidos)}</strong></div>"
                        "</div>",
                        unsafe_allow_html=True,
                    )
            with k4:
                with st.container(border=True):
                    cor_r = "#22c55e" if rent_total_pct >= 0 else "#ef4444"
                    st.markdown(
                        "<div style='min-height:92px; display:flex; flex-direction:column; justify-content:space-between;'>"
                        "<div style='font-size:13px; opacity:0.78;'>📈 Rentabilidade (c/ dividendos)</div>"
                        f"<div style='font-size:23px; font-weight:700; color:{cor_r}; line-height:1.25;'>{rent_total_pct:+.2f}%</div>"
                        f"<div style='font-size:12.5px; opacity:0.82;'>Variação pura do preço: <strong>{var_cart_pct:+.2f}%</strong></div>"
                        "</div>",
                        unsafe_allow_html=True,
                    )

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
                        barmode="relative", height=305, margin=dict(l=10, r=68, t=36, b=24),
                        paper_bgcolor="rgba(0,0,0,0)", plot_bgcolor="rgba(0,0,0,0)",
                        dragmode="pan",
                        yaxis=dict(
                            side="right", showgrid=True, gridcolor="rgba(128,128,128,0.22)", tickprefix="R$ ",
                            showspikes=True, spikemode="across", spikesnap="cursor", spikethickness=1,
                            spikecolor="rgba(148,163,184,0.55)", spikedash="dash",
                        ),
                        xaxis=dict(
                            showgrid=False,
                            showspikes=True, spikemode="across", spikesnap="cursor", spikethickness=1,
                            spikecolor="rgba(148,163,184,0.55)", spikedash="dash",
                        ),
                        legend=dict(orientation="h", yanchor="bottom", y=1.02, xanchor="center", x=0.5),
                    )
                    st.plotly_chart(
                        fig_ev,
                        use_container_width=True,
                        config={"scrollZoom": True, "displaylogo": False, "modeBarButtonsToRemove": ["zoom2d", "zoomIn2d", "zoomOut2d", "lasso2d", "select2d"]},
                    )
                    st.caption("💡 DEXTools: Segure **Shift + Botão Esquerdo e arraste** (ou clique em **📏 Medir**) para medir a variação (%).")

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
                ".cart-wrap{width:100%;overflow-x:auto;overflow-y:hidden;margin:12px 0;}"
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

            with st.expander("🧭 Assistente de Aporte Inteligente — Sugestão de Onde Aportar este Mês", expanded=False):
                ca1, ca2 = st.columns([1.4, 2.2], vertical_alignment="bottom")
                with ca1:
                    valor_aporte = st.number_input(
                        "Valor disponível para aporte este mês (R$):",
                        min_value=50.0,
                        value=1500.0,
                        step=100.0,
                        format="%.2f",
                        key="cart_aporte_valor",
                    )
                with ca2:
                    op_origem_ap = [
                        "Aportar apenas em ativos já presentes na carteira",
                        "Permitir sugestões incluindo minhas Ações Favoritas",
                    ]
                    origem_ap = st.radio(
                        "Universo de sugestões:",
                        options=op_origem_ap,
                        index=0,
                        horizontal=True,
                        key="cart_aporte_origem",
                    )

                incluir_favs_ap = (origem_ap == op_origem_ap[1])
                pool_bruto = [dict(x) for x in itens_tabela_cart]
                tks_no_pool = {x["ticker"] for x in pool_bruto}

                if incluir_favs_ap:
                    favs_extras = [tf for tf in st.session_state.get("favoritos", []) if tf not in tks_no_pool and tf in mapa_todos]
                    if favs_extras:
                        falt_fy = tuple(t for t in favs_extras if t not in dados_yf)
                        if falt_fy:
                            dados_yf.update(buscar_yahoo_lote(falt_fy))
                        falt_fn = tuple(t for t in favs_extras if t not in dados_news)
                        if falt_fn:
                            dados_news.update(buscar_sentimento_noticias_lote(falt_fn))
                        falt_fi = tuple(t for t in favs_extras if t not in dados_i10)
                        if falt_fi:
                            dados_i10.update(buscar_investidor10_lote(falt_fi))
                        for tf in favs_extras:
                            it_fav_ap = montar_item_completo(mapa_todos[tf])
                            it_fav_ap["saldo"] = 0.0
                            pool_bruto.append(it_fav_ap)

                chave_sc_ap = {
                    "🏆 Geral (Melhor Compra Equilibrada)": "score_geral",
                    "🏛️ Longo Prazo (Fundamentos & Dividendos)": "score_lp",
                    "⚡ Curto Prazo (Timing & Catalisadores)": "score_cp",
                }.get(st.session_state.get("tab1_modo_score_val", ""), "score_geral")

                elegiveis_ap = [
                    x for x in pool_bruto
                    if float(x.get("cotacao") or 0.0) > 0.0
                    and not x.get("eh_value_trap")
                    and not str(x.get("veredito", "")).startswith(("🔴 Crítico", "🟣 Esticado"))
                ]

                if not elegiveis_ap:
                    st.warning(
                        "⚠️ Nenhum ativo elegível para aporte seguro no momento: os ativos avaliados estão "
                        "classificados como **🔴 Crítico** ou **🟣 Esticado**. Considere aguardar melhores pontos de entrada."
                    )
                else:
                    n_base_peso = max(1, len(pool_bruto))
                    peso_alvo_eq = 100.0 / n_base_peso

                    cands_ranqueados = []
                    for c_ap in elegiveis_ap:
                        cot_ap = float(c_ap["cotacao"])
                        sc_ap = float(c_ap.get(chave_sc_ap, c_ap.get("score_geral") or 0.0))
                        teto_ap = c_ap.get("preco_teto_modelo")
                        if teto_ap and float(teto_ap) > 0.0:
                            desc_teto_pct = ((float(teto_ap) - cot_ap) / float(teto_ap)) * 100.0
                            pts_desc = max(0.0, min(100.0, ((desc_teto_pct + 20.0) / 70.0) * 100.0))
                        else:
                            desc_teto_pct = c_ap.get("avg_ms")
                            pts_desc = max(0.0, min(100.0, (((desc_teto_pct or 0.0) + 20.0) / 70.0) * 100.0))

                        saldo_ap = float(c_ap.get("saldo") or 0.0)
                        peso_atual_ap = (saldo_ap / total_atual * 100.0) if total_atual > 0.0 else 0.0
                        gap_peso = max(0.0, peso_alvo_eq - peso_atual_ap)
                        pts_rebal = min(100.0, (gap_peso / max(5.0, peso_alvo_eq)) * 100.0)

                        prioridade = (0.50 * sc_ap) + (0.30 * pts_desc) + (0.20 * pts_rebal)
                        cands_ranqueados.append({
                            **c_ap,
                            "_prioridade": prioridade,
                            "_sc_ativo": sc_ap,
                            "_desc_teto_pct": desc_teto_pct,
                            "_peso_atual": peso_atual_ap,
                            "_eh_novo_fav": (saldo_ap == 0.0),
                        })

                    cands_ranqueados.sort(key=lambda x: x["_prioridade"], reverse=True)
                    compraveis = [c for c in cands_ranqueados if float(c["cotacao"]) <= valor_aporte]

                    if not compraveis:
                        menor_px = min(float(c["cotacao"]) for c in cands_ranqueados)
                        st.info(
                            f"O valor disponível (R$ {fmt_num(valor_aporte)}) é inferior à cotação do ativo elegível "
                            f"mais acessível (R$ {fmt_num(menor_px)})."
                        )
                    else:
                        top_ap = compraveis[:3]
                        pesos_dist = {1: [1.0], 2: [0.60, 0.40], 3: [0.45, 0.35, 0.20]}[len(top_ap)]

                        qtds_ap = [0] * len(top_ap)
                        saldo_restante = float(valor_aporte)

                        # Pass 1: distribuição proporcional inicial
                        for idx_a, (cand_a, w_a) in enumerate(zip(top_ap, pesos_dist)):
                            fatia = valor_aporte * w_a
                            px_a = float(cand_a["cotacao"])
                            q_a = int(min(fatia, saldo_restante) // px_a)
                            if q_a > 0:
                                qtds_ap[idx_a] += q_a
                                saldo_restante -= q_a * px_a

                        # Pass 2: aproveitamento do troco priorizando os melhores ranqueados
                        comprou_extra = True
                        while comprou_extra:
                            comprou_extra = False
                            for idx_a, cand_a in enumerate(top_ap):
                                px_a = float(cand_a["cotacao"])
                                if saldo_restante >= px_a:
                                    qtds_ap[idx_a] += 1
                                    saldo_restante -= px_a
                                    comprou_extra = True

                        sugestoes_finais = []
                        total_alocado = 0.0
                        for idx_a, cand_a in enumerate(top_ap):
                            q_f = qtds_ap[idx_a]
                            if q_f <= 0:
                                continue
                            px_a = float(cand_a["cotacao"])
                            custo_lote = q_f * px_a
                            total_alocado += custo_lote

                            motivos_ap = []
                            dt_pct = cand_a["_desc_teto_pct"]
                            if dt_pct is not None:
                                if dt_pct >= 0:
                                    motivos_ap.append(f"desconto de {fmt_num(dt_pct, 1)}% frente ao teto")
                                else:
                                    motivos_ap.append(f"{fmt_num(abs(dt_pct), 1)}% acima do teto conservador")
                            if cand_a["_eh_novo_fav"]:
                                motivos_ap.append("nova entrada via Favoritas")
                            elif cand_a["_peso_atual"] < peso_alvo_eq:
                                motivos_ap.append(f"rebalanceamento (peso atual {fmt_num(cand_a['_peso_atual'], 1)}%)")
                            ifr_a = cand_a.get("ifr_14")
                            if ifr_a is not None and 30.0 <= float(ifr_a) <= 48.0:
                                motivos_ap.append(f"IFR favorável ({fmt_num(ifr_a, 1)})")
                            motivos_ap.append(f"Score {fmt_num(cand_a['_sc_ativo'], 1)}/100")

                            teto_a = cand_a.get("preco_teto_modelo")
                            teto_a_txt = f"R$ {fmt_num(teto_a)}" if (teto_a and float(teto_a) > 0) else "—"
                            sugestoes_finais.append({
                                "cand": cand_a,
                                "qtd": q_f,
                                "custo": custo_lote,
                                "teto_txt": teto_a_txt,
                                "motivo": "; ".join(motivos_ap).capitalize() + ".",
                            })

                        pct_alocado = (total_alocado / valor_aporte * 100.0) if valor_aporte > 0 else 0.0
                        ap_m1, ap_m2, ap_m3 = st.columns(3)
                        ap_m1.metric("💵 Valor Disponível", f"R$ {fmt_num(valor_aporte)}")
                        ap_m2.metric("✅ Total Alocado", f"R$ {fmt_num(total_alocado)}", f"{fmt_num(pct_alocado, 1)}% do aporte")
                        ap_m3.metric("💰 Troco em Caixa", f"R$ {fmt_num(saldo_restante)}")

                        cols_sug = st.columns(len(sugestoes_finais))
                        for col_s, sug in zip(cols_sug, sugestoes_finais):
                            ca = sug["cand"]
                            with col_s:
                                with st.container(border=True):
                                    st.markdown(
                                        "<div style='min-height:205px; display:flex; flex-direction:column; justify-content:space-between;'>"
                                        "<div>"
                                        f"<div style='font-size:19px; font-weight:700; color:#60a5fa;'>{ca['ticker']}</div>"
                                        f"<div style='font-size:12px; opacity:0.8; margin-bottom:6px; white-space:nowrap; overflow:hidden; text-overflow:ellipsis;' title='{html.escape(ca['nome'])}'>{html.escape(ca['nome'])}</div>"
                                        f"<div style='margin-bottom:6px;'>{badge_veredito_html(ca.get('veredito', ''))}</div>"
                                        f"<div style='font-size:15px; font-weight:700; color:#22c55e;'>Comprar: {sug['qtd']} ações</div>"
                                        f"<div style='font-size:14px; margin-bottom:6px;'>Custo do lote: <strong>R$ {fmt_num(sug['custo'])}</strong></div>"
                                        f"<div style='font-size:12px; opacity:0.9;'>Cotação: <strong>R$ {fmt_num(ca['cotacao'])}</strong> vs Teto: <strong>{sug['teto_txt']}</strong></div>"
                                        "</div>"
                                        f"<div style='font-size:12px; opacity:0.85; margin-top:8px;'>📝 {html.escape(sug['motivo'])}</div>"
                                        "</div>",
                                        unsafe_allow_html=True,
                                    )

            with st.expander("🔎 Abrir Gráfico & Histórico Fundamentalista de um ativo da carteira", expanded=False):
                tk_c_sel = st.selectbox("Escolha o ativo da carteira:", options=[x["ticker"] for x in itens_tabela_cart], key="cart_raiox_sel")
                it_c_sel = next(x for x in itens_tabela_cart if x["ticker"] == tk_c_sel)
                render_grafico_e_tabela_ativo(tk_c_sel, it_c_sel["nome"], base_ativo=it_c_sel, key_prefix="cart_rx")

        st.markdown("---")
        c_l1, c_l2 = st.columns([3.5, 1.3], vertical_alignment="top")
        with c_l2:
            if st.button("➕ Adicionar Lançamento", type="primary", use_container_width=True, key="btn_add_bot"):
                modal_adicionar_lancamento(tickers_b3)

        with c_l1:
            with st.expander(f"🧾 Lançamentos ({len(st.session_state['lancamentos'])}) & Backup CSV", expanded=False):
                if st.session_state["lancamentos"]:
                    df_l = pd.DataFrame(st.session_state["lancamentos"])
                    st.dataframe(df_l, use_container_width=True)
                    c_del, c_limp, c_dl = st.columns([2, 1, 1.2], vertical_alignment="bottom")
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

st.markdown(
    "<style>"
    ".js-plotly-plot .plotly .modebar{top:-2px!important;right:4px!important;background:transparent!important;}"
    ".tv-measure-overlay{position:absolute;inset:0;pointer-events:none;z-index:60;overflow:visible;}"
    ".tv-measure-svg{position:absolute;inset:0;width:100%;height:100%;overflow:visible;pointer-events:none;}"
    ".tv-measure-pill-btn{position:absolute;bottom:2px;right:6px;z-index:66;pointer-events:auto;"
    "padding:2px 8px;border-radius:6px;font-size:10.5px;font-weight:600;cursor:pointer;user-select:none;"
    "background:rgba(30,41,59,0.78);color:#cbd5e1;border:1px solid rgba(148,163,184,0.35);"
    "backdrop-filter:blur(4px);transition:all 0.15s ease;}"
    ".tv-measure-pill-btn:hover{border-color:#60a5fa;color:#ffffff;}"
    ".tv-measure-pill-btn.armed{background:#2563eb;color:#ffffff;border-color:#60a5fa;}"
    ".tv-measure-card{position:absolute;pointer-events:auto;padding:7px 11px;border-radius:7px;"
    "color:#ffffff;font-family:system-ui,-apple-system,sans-serif;font-size:12px;line-height:1.38;"
    "font-weight:600;box-shadow:0 6px 18px rgba(0,0,0,0.45);white-space:nowrap;z-index:68;user-select:none;}"
    ".tv-measure-card-head{display:flex;align-items:center;justify-content:space-between;gap:10px;}"
    ".tv-measure-close{cursor:pointer;font-size:13px;line-height:1;opacity:0.85;padding:0 2px;}"
    ".tv-measure-close:hover{opacity:1;}"
    ".tv-measure-tag{position:absolute;pointer-events:none;padding:1px 6px;border-radius:4px;"
    "font-size:10.5px;font-weight:700;color:#ffffff;white-space:nowrap;box-shadow:0 2px 6px rgba(0,0,0,0.35);z-index:62;}"
    "</style>",
    unsafe_allow_html=True,
)

_usa_st_html_m = hasattr(st, "html") and "unsafe_allow_javascript" in inspect.signature(st.html).parameters
_js_chart_measure = """
<script>
(function() {
    const pWin = __USE_PARENT__ ? window.parent : window;
    const pDoc = pWin.document;
    const SVG_NS = "http://www.w3.org/2000/svg";

    function fmtNumBr(v, dec) {
        if (!Number.isFinite(v)) return "—";
        return v.toLocaleString("pt-BR", { minimumFractionDigits: dec, maximumFractionDigits: dec });
    }

    function isCartesianPlot(gd) {
        if (!gd || !gd._fullLayout) return false;
        const xa = gd._fullLayout.xaxis;
        const ya = gd._fullLayout.yaxis;
        return !!(xa && ya && (typeof xa.c2p === "function" || Array.isArray(xa.range)));
    }

    function getDragEl(gd) {
        return gd.querySelector(".nsewdrag") || gd.querySelector("rect.drag") || gd;
    }

    function axisD2C(ax, d) {
        if (typeof ax.d2c === "function") return ax.d2c(d);
        if (ax.type === "log") return Math.log10(Number(d));
        if (ax.type === "date") return new Date(d).getTime();
        return Number(d);
    }

    function axisC2D(ax, c) {
        if (ax.type === "log") return Math.pow(10, c);
        if (typeof ax.c2d === "function") return ax.c2d(c);
        return c;
    }

    function toPxX(ax, c, width) {
        if (typeof ax.c2p === "function") return ax.c2p(c);
        const r0 = axisD2C(ax, ax.range[0]);
        const r1 = axisD2C(ax, ax.range[1]);
        const len = ax._length || width || 1;
        return ((c - r0) / (r1 - r0 || 1)) * len;
    }

    function toPxY(ax, c, height) {
        if (typeof ax.c2p === "function") return ax.c2p(c);
        const r0 = axisD2C(ax, ax.range[0]);
        const r1 = axisD2C(ax, ax.range[1]);
        const len = ax._length || height || 1;
        return len - ((c - r0) / (r1 - r0 || 1)) * len;
    }

    function toCoordX(ax, px, width) {
        if (typeof ax.p2c === "function") return ax.p2c(px);
        const r0 = axisD2C(ax, ax.range[0]);
        const r1 = axisD2C(ax, ax.range[1]);
        const len = ax._length || width || 1;
        return r0 + (px / len) * (r1 - r0);
    }

    function toCoordY(ax, py, height) {
        if (typeof ax.p2c === "function") return ax.p2c(py);
        const r0 = axisD2C(ax, ax.range[0]);
        const r1 = axisD2C(ax, ax.range[1]);
        const len = ax._length || height || 1;
        return r1 - (py / len) * (r1 - r0);
    }

    function formatXDisplay(ax, pt) {
        if (ax.type === "category") {
            const cats = ax._categories || [];
            const idx = Math.max(0, Math.min(cats.length - 1, Math.round(pt.cx)));
            return cats[idx] !== undefined ? String(cats[idx]) : "";
        }
        if (ax.type === "date") {
            const raw = pt.rawX !== undefined ? String(pt.rawX) : String(axisC2D(ax, pt.cx) || "");
            const m = raw.match(/^(\\d{4})-(\\d{2})-(\\d{2})(?:[T\\s](\\d{2}):(\\d{2}))?/);
            if (m) {
                const base = m[3] + "/" + m[2] + "/" + m[1];
                return (m[4] && m[5] && !(m[4] === "00" && m[5] === "00")) ? (base + " " + m[4] + ":" + m[5]) : base;
            }
            return raw;
        }
        return fmtNumBr(Number(axisC2D(ax, pt.cx)), 2);
    }

    function pointFromEvent(gd, e) {
        const dragEl = getDragEl(gd);
        const rect = dragEl.getBoundingClientRect();
        const px = Math.max(0, Math.min(rect.width, e.clientX - rect.left));
        const py = Math.max(0, Math.min(rect.height, e.clientY - rect.top));
        const xa = gd._fullLayout.xaxis;
        const ya = gd._fullLayout.yaxis;

        let bestPt = null;
        let bestDist = Infinity;
        const calcArr = gd.calcdata || [];
        const dataArr = gd.data || [];
        const visibleCnt = dataArr.filter(function(t) { return t && t.visible !== false && t.visible !== "legendonly" && t.hoverinfo !== "skip"; }).length;
        const maxDy = visibleCnt <= 1 ? 36 : 22;

        for (let ti = 0; ti < calcArr.length; ti++) {
            const tr = dataArr[ti];
            const pts = calcArr[ti];
            if (!tr || !pts || !pts.length) continue;
            if (tr.visible === false || tr.visible === "legendonly" || tr.type === "pie" || tr.hoverinfo === "skip") continue;
            const rawXs = Array.isArray(tr.x) ? tr.x : null;

            for (let i = 0; i < pts.length; i++) {
                const cpt = pts[i];
                if (!cpt) continue;
                const ptCx = cpt.x;
                const ptCy = Number.isFinite(cpt.close) ? cpt.close : (Number.isFinite(cpt.c) ? cpt.c : cpt.y);
                if (!Number.isFinite(ptCx) || !Number.isFinite(ptCy)) continue;

                const ptPx = toPxX(xa, ptCx, rect.width);
                const ptPy = toPxY(ya, ptCy, rect.height);
                const dx = ptPx - px;
                const dy = ptPy - py;
                if (Math.abs(dy) <= maxDy && Math.abs(dx) <= 24) {
                    const dist = Math.hypot(dx, dy);
                    if (dist < bestDist) {
                        bestDist = dist;
                        const valYNum = Number(axisC2D(ya, ptCy));
                        bestPt = {
                            cx: ptCx,
                            cy: ptCy,
                            valY: Number.isFinite(valYNum) ? valYNum : ptCy,
                            rawX: rawXs ? rawXs[i] : undefined,
                            idx: i,
                            traceIdx: ti,
                            snapped: true
                        };
                    }
                }
            }
        }

        if (bestPt) return bestPt;

        const cx = toCoordX(xa, px, rect.width);
        const cy = toCoordY(ya, py, rect.height);
        const valY = Number(axisC2D(ya, cy));
        return {
            cx: cx,
            cy: cy,
            valY: Number.isFinite(valY) ? valY : cy,
            rawX: undefined,
            idx: null,
            traceIdx: null,
            snapped: false
        };
    }

    function svgEl(tag, attrs) {
        const el = pDoc.createElementNS(SVG_NS, tag);
        if (attrs) {
            Object.keys(attrs).forEach(function(k) {
                el.setAttribute(k, String(attrs[k]));
            });
        }
        return el;
    }

    function updateToolbarBtn(gd) {
        if (!gd) return;
        const btn = gd.querySelector(".tv-measure-pill-btn");
        if (!btn) return;
        const armed = !!gd.__measureArmed;
        const active = !!(gd.__measureState && gd.__measureState.state === "measuring");
        if (armed || active) {
            btn.classList.add("armed");
            btn.textContent = "📏 Medindo... (arraste ou clique 2 pts)";
        } else {
            btn.classList.remove("armed");
            btn.textContent = "📏 Medir (Shift+Arrastar)";
        }
    }

    function clearMeasure(gd) {
        if (!gd) return;
        gd.__measureState = null;
        gd.__measureArmed = false;
        const ov = gd.querySelector(".tv-measure-overlay");
        if (ov) ov.replaceChildren();
        if (pWin.__activeMeasuringGd === gd) {
            pWin.__activeMeasuringGd = null;
        }
        updateToolbarBtn(gd);
    }

    function renderMeasure(gd) {
        if (!gd || !isCartesianPlot(gd)) return;
        updateToolbarBtn(gd);
        const stM = gd.__measureState;
        let ov = gd.querySelector(".tv-measure-overlay");
        if (!stM || !stM.p1 || !stM.p2) {
            if (ov) ov.replaceChildren();
            return;
        }
        if (!ov) {
            if (getComputedStyle(gd).position === "static") {
                gd.style.position = "relative";
            }
            ov = pDoc.createElement("div");
            ov.className = "tv-measure-overlay";
            gd.appendChild(ov);
        }

        const dragEl = getDragEl(gd);
        const gdRect = gd.getBoundingClientRect();
        const dragRect = dragEl.getBoundingClientRect();
        if (!dragRect.width || !dragRect.height) return;

        const offL = dragRect.left - gdRect.left;
        const offT = dragRect.top - gdRect.top;
        const xa = gd._fullLayout.xaxis;
        const ya = gd._fullLayout.yaxis;

        const px1 = Math.max(0, Math.min(dragRect.width, toPxX(xa, stM.p1.cx, dragRect.width)));
        const py1 = Math.max(0, Math.min(dragRect.height, toPxY(ya, stM.p1.cy, dragRect.height)));
        const px2 = Math.max(0, Math.min(dragRect.width, toPxX(xa, stM.p2.cx, dragRect.width)));
        const py2 = Math.max(0, Math.min(dragRect.height, toPxY(ya, stM.p2.cy, dragRect.height)));

        const x1 = offL + px1;
        const y1 = offT + py1;
        const x2 = offL + px2;
        const y2 = offT + py2;

        const rx = Math.min(x1, x2);
        const ry = Math.min(y1, y2);
        const rw = Math.max(1, Math.abs(x2 - x1));
        const rh = Math.max(1, Math.abs(y2 - y1));

        const v1 = stM.p1.valY;
        const v2 = stM.p2.valY;
        const diff = v2 - v1;
        const pref = ya.tickprefix || "";
        const suf = ya.ticksuffix || "";

        let pct = 0;
        if (suf === "%") {
            const base1 = 1 + (v1 / 100);
            pct = base1 > 0.0001 ? (((1 + (v2 / 100)) / base1) - 1) * 100 : diff;
        } else {
            pct = Math.abs(v1) > 1e-9 ? (diff / Math.abs(v1)) * 100 : 0;
        }

        const ehAlta = diff >= 0;
        const corMain = ehAlta ? "#16a34a" : "#e11d48";
        const corStroke = ehAlta ? "rgba(34, 197, 94, 0.90)" : "rgba(244, 63, 94, 0.90)";
        const corFill = ehAlta ? "rgba(34, 197, 94, 0.18)" : "rgba(244, 63, 94, 0.18)";
        const sinalD = diff > 0 ? "+" : "";
        const sinalP = pct > 0 ? "+" : "";

        const v1Fmt = pref + fmtNumBr(v1, 2) + suf;
        const v2Fmt = pref + fmtNumBr(v2, 2) + suf;
        const diffFmt = (suf === "%")
            ? (sinalD + fmtNumBr(diff, 2) + " p.p. (" + sinalP + fmtNumBr(pct, 2) + "%)")
            : (sinalD + pref + fmtNumBr(diff, 2) + suf + " (" + sinalP + fmtNumBr(pct, 2) + "%)");

        const xLbl1 = formatXDisplay(xa, stM.p1);
        const xLbl2 = formatXDisplay(xa, stM.p2);
        let spanTxt = "";
        if (xa.type === "date") {
            const msDiff = Math.abs(stM.p2.cx - stM.p1.cx);
            const dias = Math.round(msDiff / 86400000);
            const hrs = Math.round(msDiff / 3600000);
            const dur = dias >= 1 ? (dias + "d") : (hrs >= 1 ? (hrs + "h") : (Math.round(msDiff / 60000) + "min"));
            if (stM.p1.snapped && stM.p2.snapped && stM.p1.traceIdx === stM.p2.traceIdx && stM.p1.idx !== null && stM.p2.idx !== null) {
                const pts = Math.abs(stM.p2.idx - stM.p1.idx);
                spanTxt = pts + " pts · " + dur;
            } else {
                spanTxt = dur;
            }
            if (xLbl1 && xLbl2) spanTxt = xLbl1 + " → " + xLbl2 + " (" + spanTxt + ")";
        } else if (xLbl1 && xLbl2) {
            spanTxt = xLbl1 + " → " + xLbl2;
        }

        const svg = svgEl("svg", { class: "tv-measure-svg" });
        svg.appendChild(svgEl("rect", {
            x: rx, y: ry, width: rw, height: rh,
            fill: corFill, stroke: corStroke, "stroke-width": "1.2", "stroke-dasharray": "4 3"
        }));
        svg.appendChild(svgEl("line", {
            x1: offL, y1: y1, x2: offL + dragRect.width, y2: y1,
            stroke: "rgba(148,163,184,0.45)", "stroke-width": "1", "stroke-dasharray": "3 3"
        }));
        svg.appendChild(svgEl("line", {
            x1: offL, y1: y2, x2: offL + dragRect.width, y2: y2,
            stroke: corStroke, "stroke-width": "1", "stroke-dasharray": "3 3"
        }));

        const midX = rx + rw / 2;
        const midY = ry + rh / 2;
        if (rh > 14) {
            svg.appendChild(svgEl("line", {
                x1: midX, y1: y1, x2: midX, y2: y2,
                stroke: corStroke, "stroke-width": "1.6"
            }));
            const dirV = y2 >= y1 ? 1 : -1;
            svg.appendChild(svgEl("polygon", {
                points: midX + "," + y2 + " " + (midX - 5) + "," + (y2 - 7 * dirV) + " " + (midX + 5) + "," + (y2 - 7 * dirV),
                fill: corStroke
            }));
        }
        if (rw > 14) {
            svg.appendChild(svgEl("line", {
                x1: x1, y1: midY, x2: x2, y2: midY,
                stroke: corStroke, "stroke-width": "1.6"
            }));
            const dirH = x2 >= x1 ? 1 : -1;
            svg.appendChild(svgEl("polygon", {
                points: x2 + "," + midY + " " + (x2 - 7 * dirH) + "," + (midY - 5) + " " + (x2 - 7 * dirH) + "," + (midY + 5),
                fill: corStroke
            }));
        }

        svg.appendChild(svgEl("circle", {
            cx: x1, cy: y1, r: "4.5", fill: "#3b82f6", stroke: "#ffffff", "stroke-width": "1.5"
        }));
        svg.appendChild(svgEl("circle", {
            cx: x2, cy: y2, r: "4.8", fill: corMain, stroke: "#ffffff", "stroke-width": "1.5"
        }));

        const tagSideX = ya.side === "right" ? (offL + dragRect.width + 4) : Math.max(2, offL - 66);
        const tag1 = pDoc.createElement("div");
        tag1.className = "tv-measure-tag";
        tag1.style.left = tagSideX + "px";
        tag1.style.top = Math.max(0, y1 - 10) + "px";
        tag1.style.background = "#2563eb";
        tag1.textContent = v1Fmt;

        const tag2 = pDoc.createElement("div");
        tag2.className = "tv-measure-tag";
        tag2.style.left = tagSideX + "px";
        tag2.style.top = Math.max(0, y2 - 10) + "px";
        tag2.style.background = corMain;
        tag2.textContent = v2Fmt;

        const cardWEst = 240;
        const cardLeft = Math.max(offL + 4, Math.min(offL + dragRect.width - cardWEst, midX - 110));
        const abaixo = (ry + rh + 64 <= offT + dragRect.height + 10);
        const cardTop = abaixo ? (ry + rh + 8) : Math.max(offT + 4, ry - 64);

        const card = pDoc.createElement("div");
        card.className = "tv-measure-card";
        card.style.left = cardLeft + "px";
        card.style.top = cardTop + "px";
        card.style.background = corMain;

        const head = pDoc.createElement("div");
        head.className = "tv-measure-card-head";
        const spanDiff = pDoc.createElement("span");
        spanDiff.textContent = diffFmt;
        const closeBtn = pDoc.createElement("span");
        closeBtn.className = "tv-measure-close";
        closeBtn.title = "Fechar medição (Esc)";
        closeBtn.textContent = "✕";
        head.appendChild(spanDiff);
        head.appendChild(closeBtn);

        const valsDiv = pDoc.createElement("div");
        valsDiv.style.fontSize = "11px";
        valsDiv.style.opacity = "0.95";
        valsDiv.style.fontWeight = "500";
        valsDiv.textContent = v1Fmt + " → " + v2Fmt;

        const subDiv = pDoc.createElement("div");
        subDiv.style.fontSize = "10.5px";
        subDiv.style.opacity = "0.9";
        subDiv.textContent = stM.state === "measuring"
            ? "Solte o arraste ou clique no ponto final"
            : spanTxt;

        card.appendChild(head);
        card.appendChild(valsDiv);
        if (subDiv.textContent) card.appendChild(subDiv);

        ov.replaceChildren(svg, tag1, tag2, card);
    }

    function attachPlot(gd) {
        if (!gd || !isCartesianPlot(gd)) return;
        if (getComputedStyle(gd).position === "static") {
            gd.style.position = "relative";
        }
        if (!gd.querySelector(".tv-measure-pill-btn")) {
            const btn = pDoc.createElement("div");
            btn.className = "tv-measure-pill-btn";
            btn.title = "Ativar régua de variação (%) — ou segure Shift + Botão Esquerdo e arraste no gráfico";
            btn.textContent = "📏 Medir (Shift+Arrastar)";
            gd.appendChild(btn);
        }
        if (gd.dataset.measureReady === "1") return;
        gd.dataset.measureReady = "1";
        if (typeof gd.on === "function") {
            gd.on("plotly_relayout", function() { renderMeasure(gd); });
            gd.on("plotly_afterplot", function() {
                attachPlot(gd);
                renderMeasure(gd);
            });
        }
    }

    function scanPlots() {
        pDoc.querySelectorAll(".js-plotly-plot").forEach(attachPlot);
    }

    scanPlots();

    if (!pWin.__chartMeasureObserver) {
        let tm = null;
        pWin.__chartMeasureObserver = new MutationObserver(function() {
            if (tm) clearTimeout(tm);
            tm = setTimeout(function() {
                tm = null;
                scanPlots();
            }, 80);
        });
        pWin.__chartMeasureObserver.observe(pDoc.body, { childList: true, subtree: true });
    }

    if (!pWin.__chartMeasureAttachedV2) {
        pWin.__chartMeasureAttachedV2 = true;

        function blockEvent(e) {
            e.preventDefault();
            e.stopPropagation();
            if (typeof e.stopImmediatePropagation === "function") {
                e.stopImmediatePropagation();
            }
        }

        function onDownEvent(e) {
            if (e.button !== 0) return;

            const pillBtn = e.target && e.target.closest ? e.target.closest(".tv-measure-pill-btn") : null;
            if (pillBtn) {
                blockEvent(e);
                if (e.type === "pointerdown") {
                    const gdP = pillBtn.closest(".js-plotly-plot");
                    if (gdP) {
                        if (gdP.__measureArmed || (gdP.__measureState && gdP.__measureState.state === "measuring")) {
                            clearMeasure(gdP);
                        } else {
                            clearMeasure(gdP);
                            gdP.__measureArmed = true;
                            updateToolbarBtn(gdP);
                        }
                    }
                }
                return;
            }

            const closeBtn = e.target && e.target.closest ? e.target.closest(".tv-measure-close") : null;
            if (closeBtn) {
                blockEvent(e);
                if (e.type === "pointerdown") {
                    clearMeasure(closeBtn.closest(".js-plotly-plot"));
                }
                return;
            }

            const gd = e.target && e.target.closest ? e.target.closest(".js-plotly-plot") : null;
            if (!gd) return;

            if (e.shiftKey) {
                blockEvent(e);
            }
            if (!isCartesianPlot(gd)) return;
            attachPlot(gd);

            const dragEl = getDragEl(gd);
            const rect = dragEl.getBoundingClientRect();
            const dentro = e.clientX >= rect.left - 6 && e.clientX <= rect.right + 6 && e.clientY >= rect.top - 6 && e.clientY <= rect.bottom + 6;
            if (!dentro) return;

            if (pWin.__activeMeasuringGd && pWin.__activeMeasuringGd === gd && gd.__measureState && gd.__measureState.state === "measuring") {
                blockEvent(e);
                if (e.type === "pointerdown") {
                    pWin.__suppressPlotClickUntil = Date.now() + 400;
                    gd.__measureState.p2 = pointFromEvent(gd, e);
                    gd.__measureState.state = "locked";
                    pWin.__activeMeasuringGd = null;
                    renderMeasure(gd);
                }
                return;
            }

            if (e.shiftKey || gd.__measureArmed) {
                blockEvent(e);
                if (e.type === "pointerdown") {
                    gd.__measureArmed = false;
                    pWin.__suppressPlotClickUntil = Date.now() + 400;
                    if (pWin.__activeMeasuringGd && pWin.__activeMeasuringGd !== gd) {
                        clearMeasure(pWin.__activeMeasuringGd);
                    }
                    const p1 = pointFromEvent(gd, e);
                    gd.__measureState = {
                        state: "measuring",
                        p1: p1,
                        p2: p1,
                        startX: e.clientX,
                        startY: e.clientY
                    };
                    pWin.__activeMeasuringGd = gd;
                    renderMeasure(gd);
                }
                return;
            }

            if (e.type === "pointerdown" && gd.__measureState && gd.__measureState.state === "locked") {
                const insideCard = e.target && e.target.closest ? e.target.closest(".tv-measure-card") : null;
                if (!insideCard) {
                    gd.__pendingClearStart = { x: e.clientX, y: e.clientY };
                }
            }
        }

        pWin.addEventListener("pointerdown", onDownEvent, true);
        pWin.addEventListener("mousedown", onDownEvent, true);

        pWin.addEventListener("pointermove", function(e) {
            const gd = pWin.__activeMeasuringGd;
            if (!gd || !gd.__measureState || gd.__measureState.state !== "measuring") return;
            blockEvent(e);
            gd.__measureState.p2 = pointFromEvent(gd, e);
            renderMeasure(gd);
        }, true);

        pWin.addEventListener("mousemove", function(e) {
            const gd = pWin.__activeMeasuringGd;
            if (gd && gd.__measureState && gd.__measureState.state === "measuring") {
                blockEvent(e);
            }
        }, true);

        pWin.addEventListener("pointerup", function(e) {
            if (e.button !== 0) return;
            const gd = pWin.__activeMeasuringGd;
            if (gd && gd.__measureState && gd.__measureState.state === "measuring") {
                const dist = Math.hypot(e.clientX - gd.__measureState.startX, e.clientY - gd.__measureState.startY);
                if (dist >= 6) {
                    blockEvent(e);
                    pWin.__suppressPlotClickUntil = Date.now() + 400;
                    gd.__measureState.p2 = pointFromEvent(gd, e);
                    gd.__measureState.state = "locked";
                    pWin.__activeMeasuringGd = null;
                    renderMeasure(gd);
                }
                return;
            }
            pDoc.querySelectorAll(".js-plotly-plot").forEach(function(plotEl) {
                if (plotEl.__pendingClearStart) {
                    const infoC = plotEl.__pendingClearStart;
                    plotEl.__pendingClearStart = null;
                    if (Math.hypot(e.clientX - infoC.x, e.clientY - infoC.y) < 6) {
                        clearMeasure(plotEl);
                    }
                }
            });
        }, true);

        pWin.addEventListener("mouseup", function(e) {
            if (e.shiftKey || pWin.__activeMeasuringGd) {
                const gd = e.target && e.target.closest ? e.target.closest(".js-plotly-plot") : null;
                if (gd || pWin.__activeMeasuringGd) {
                    blockEvent(e);
                }
            }
        }, true);

        pWin.addEventListener("click", function(e) {
            if (pWin.__suppressPlotClickUntil && Date.now() < pWin.__suppressPlotClickUntil) {
                const gd = e.target && e.target.closest ? e.target.closest(".js-plotly-plot") : null;
                if (gd) {
                    blockEvent(e);
                }
            }
        }, true);

        pWin.addEventListener("keydown", function(e) {
            if (e.key === "Escape") {
                pDoc.querySelectorAll(".js-plotly-plot").forEach(function(gd) {
                    if (gd.__measureState || gd.__measureArmed) clearMeasure(gd);
                });
            }
        }, true);
    }
})();
</script>
""".replace("__USE_PARENT__", "false" if _usa_st_html_m else "true")

if _usa_st_html_m:
    st.html(_js_chart_measure, unsafe_allow_javascript=True)
else:
    components.html(_js_chart_measure, height=0)

st.divider()
st.caption("Aviso: Estudo quantitativo e educacional com dados obtidos via Fundamentus, CVM Dados Abertos e Yahoo Finance. Não constitui recomendação oficial de compra ou venda.")
