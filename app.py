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
def _eh_pagina_seo_ou_irrelevante(titulo: str, fonte: str = "", link: str = "") -> bool:
    t = _norm_txt(titulo)
    f = _norm_txt(fonte)
    l = _norm_txt(link)
    if not t:
        return True

    padroes_seo_exatos = (
        "resultados, dividendos", "dividendos, cotacao", "cotacao e indicadores",
        "cotacao, dividendos", "indicadores, dividendos", "cotacao, graficos",
        "preco alvo, dividendos", "valor justo e dividendos", "o que saber antes",
        "cotacao hoje, dividendos", "cotacao de hoje", "graficos e noticias",
        "acoes - cotacao", "ficha tecnica", "raiox completo", "raio-x completo",
        "veja o calendario", "historico de cotacoes",
    )
    if any(p in t for p in padroes_seo_exatos):
        return True

    kws_ficha = ("resultados", "dividendos", "cotacao", "indicadores", "balancos", "graficos", "proventos", "valuation", "historico")
    hits_ficha = sum(1 for k in kws_ficha if re.search(rf"\b{k}\b", t))
    tem_pref_ticker = bool(re.match(r"^[a-z]{4}\d{1,2}\b", t))
    if hits_ficha >= 3 or (tem_pref_ticker and hits_ficha >= 2 and not re.search(r"\b(lucro|prejuizo|aprova|anuncia|paga|corta|sobe|cai|recua|dispara|avanca|fecha|vende|compra)\b", t)):
        return True

    dominios_ficha = ("investidor10", "statusinvest", "status invest", "fundamentus", "dadosdemercado", "analisedeacoes", "investsite", "oceans14", "trademap")
    if (any(d in f for d in dominios_ficha) or any(d in l for d in dominios_ficha)) and hits_ficha >= 2:
        return True

    return False

def _fator_idade_trimestre_noticia(titulo: str, agora_ts: float | None = None) -> float:
    t = _norm_txt(titulo)
    agora_dt = datetime.fromtimestamp(agora_ts if agora_ts is not None else time.time(), tz=BRT).date()
    matches = re.findall(r"\b([1-4])\s*(?:t|tri)\s*(20\d{2}|2\d)\b", t)
    matches += re.findall(r"\b([1-4])[o°]?\s*trimestre(?:\s+de)?\s*(20\d{2}|2\d)\b", t)
    if not matches:
        return 1.0

    fim_mais_recente = None
    for tri_s, ano_s in matches:
        tri = int(tri_s)
        ano = int(ano_s) if len(ano_s) == 4 else (2000 + int(ano_s))
        if ano < 2015 or ano > agora_dt.year + 1:
            continue
        mes_fim = tri * 3
        dia_fim = 31 if mes_fim in (3, 12) else 30
        dt_fim_tri = date(ano, mes_fim, dia_fim)
        if fim_mais_recente is None or dt_fim_tri > fim_mais_recente:
            fim_mais_recente = dt_fim_tri

    if fim_mais_recente is None:
        return 1.0

    dias_passados = (agora_dt - fim_mais_recente).days
    if dias_passados > 150:
        return 0.0
    if dias_passados > 115:
        return 0.35
    return 1.0

def _classificar_sentimento_noticia(titulo: str, fonte: str = "", link: str = "") -> tuple[str, str, float]:
    if _eh_pagina_seo_ou_irrelevante(titulo, fonte=fonte, link=link):
        return "🚫 SEO/Ficha", "seo", 0.0

    t = _norm_txt(titulo)
    t_work = f" {' '.join(re.sub(r'[^a-z0-9%]+', ' ', t).split())} "

    critico_kw = (
        "recuperacao judicial", "pedido de falencia", "falencia", "fraude",
        "calote", "default", "cvm investiga", "investigada pela cvm",
        "investigacao da cvm", "pf investiga", "mpf investiga",
        "rombo", "intervencao", "liquidacao extrajudicial",
    )
    if any(k in t_work for k in critico_kw):
        return "🚨 Risco Crítico", "critico", -6.0

    pts_pos = 0.0
    pts_neg = 0.0
    teve_composto_neg_forte = False

    # 1) Expressões compostas positivas (redução de algo ruim / reversão de prejuízo)
    compostos_pos = (
        ("reverte prejuizo", 3.5),
        ("revertendo prejuizo", 3.5),
        ("sai de prejuizo", 3.5),
        ("sai do prejuizo", 3.5),
        ("saindo de prejuizo", 3.5),
        ("saindo do prejuizo", 3.5),
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

    pat_pos_flex = re.compile(
        r"\b(?:queda|reducao|diminuicao|corte)\s+(?:de|da|das|do|dos|na|nas|no|nos)\s+"
        r"(?:despesas|custos|divida|alavancagem|inadimplencia)\b"
    )
    if pat_pos_flex.search(t_work):
        pts_pos += 2.5
        t_work = pat_pos_flex.sub(" ", t_work)

    # 2) Expressões compostas negativas (aumento de algo ruim / queda ou corte de lucro, receita, margem, dividendos)
    compostos_neg = (
        ("reverte lucro", 4.5),
        ("lucro desaba", 5.0),
        ("lucro despenca", 5.0),
        ("lucro cai", 4.0),
        ("lucro recua", 3.5),
        ("lucro encolhe", 4.0),
        ("lucro diminui", 3.5),
        ("lucro baixa", 3.5),
        ("queda no lucro", 4.0),
        ("queda do lucro", 4.0),
        ("queda de lucro", 4.0),
        ("recuo no lucro", 3.5),
        ("recuo do lucro", 3.5),
        ("baixa no lucro", 3.5),
        ("corta dividendo", 4.5),
        ("corte de dividendo", 4.5),
        ("corte nos dividendos", 4.5),
        ("corta provento", 4.5),
        ("corte de provento", 4.5),
        ("reduz dividendo", 4.0),
        ("reduz provento", 4.0),
        ("suspende dividendo", 4.5),
        ("suspende provento", 4.5),
        ("duvidas sobre dividendo", 3.5),
        ("duvidas sobre provento", 3.5),
        ("dividendos em baixa", 3.5),
        ("menores dividendos", 3.5),
        ("menor dividendo", 3.5),
        ("prejuizo dispara", 4.5),
        ("prejuizo sobe", 4.0),
        ("prejuizo aumenta", 4.0),
        ("prejuizo cresce", 4.0),
        ("divida dispara", 3.5),
        ("divida sobe", 3.0),
        ("divida cresce", 3.0),
        ("divida aumenta", 3.0),
        ("inadimplencia dispara", 3.5),
        ("inadimplencia sobe", 3.0),
        ("inadimplencia cresce", 3.0),
        ("despesas sobem", 3.0),
        ("custos sobem", 3.0),
        ("receita cai", 3.5),
        ("receita recua", 3.0),
        ("queda de receita", 3.5),
        ("queda na receita", 3.5),
        ("margem cai", 3.0),
        ("margem recua", 3.0),
    )
    for frase, peso in compostos_neg:
        if frase in t_work:
            pts_neg += peso
            teve_composto_neg_forte = True
            t_work = t_work.replace(frase, " ")

    pats_neg_flex = (
        (re.compile(r"\b(?:lucro|resultado|ebitda|receita|margem|dividendo|dividendos|provento|proventos|jcp|payout)(?:\s+\w+){0,3}\s+(?:cai|cair|recua|desaba|despenca|encolhe|diminui|reduz|baixa|tomba|frustra|decepciona|pressionad[oa]|abaixo|prejuizo)\b"), 5.5),
        (re.compile(r"\b(?:queda|recuo|reducao|baixa|corte|tombo|encolhimento|duvida|duvidas|incerteza|pressao)(?:\s+\w+){0,3}\s+(?:lucro|resultado|ebitda|receita|margem|dividendo|dividendos|provento|proventos|jcp|payout)\b"), 5.5),
        (re.compile(r"\b(?:corta|cortar|reduz|reduzir|suspende|adia|cancela|limita|ameaca)(?:\s+\w+){0,3}\s+(?:dividendo|dividendos|provento|proventos|jcp|payout|distribuicao)\b"), 5.5),
    )
    for pat_nf, peso_nf in pats_neg_flex:
        if pat_nf.search(t_work):
            pts_neg += peso_nf
            teve_composto_neg_forte = True
            t_work = pat_nf.sub(" ", t_work)

    # Detecta modificadores negativos restantes na manchete para bloquear falsos positivos
    mod_neg_kws = (
        " cai ", " cair ", " queda ", " baixa ", " corta ", " corte ", " cortar ",
        " reduz ", " reducao ", " reduzir ", " duvida ", " duvidas ", " recua ", " recuo ",
        " abaixo do esperado ", " abaixo das estimativas ", " pressao ", " pressiona ",
        " pressionado ", " pressionada ", " desaba ", " despenca ", " derrete ", " tombo ",
        " frustra ", " decepciona ", " prejuizo ", " piora ", " desacelera ", " suspende ",
        " adia ", " cancela ", " rebaix", " encolhe ", " menor ", " menores ", " perda ",
        " perde ", " negativo ", " negativa ", " crise ", " multa ", " inadimpl",
    )
    tem_mod_neg = (pts_neg > 0.0) or any(k in t_work for k in mod_neg_kws)

    # 3) Fatores positivos APENAS com contexto/verbo de alta ou aprovação e sem modificadores negativos
    if not tem_mod_neg:
        pos_contexto = (
            ("lucro recorde", 3.5),
            ("resultado recorde", 3.5),
            ("supera estimativas", 3.5),
            ("acima do esperado", 3.5),
            ("bate estimativas", 3.0),
            ("lucro dispara", 3.5),
            ("lucro salta", 3.5),
            ("lucro sobe", 3.0),
            ("lucro cresce", 3.0),
            ("lucro avanca", 3.0),
            ("lucro aumenta", 3.0),
            ("melhora do resultado", 2.5),
            ("aprova dividendos", 3.0),
            ("aprova dividendo", 3.0),
            ("aprova proventos", 3.0),
            ("aprova jcp", 3.0),
            ("aprova juros sobre capital", 3.0),
            ("anuncia dividendos", 2.5),
            ("anuncia dividendo", 2.5),
            ("anuncia proventos", 2.5),
            ("anuncia jcp", 2.5),
            ("anuncia juros sobre capital", 2.5),
            ("paga dividendos", 2.5),
            ("paga jcp", 2.5),
            ("paga proventos", 2.5),
            ("distribuicao de dividendos", 2.5),
            ("distribuicao de jcp", 2.5),
            ("dividendos extraordinarios", 3.0),
            ("eleva dividendo", 3.0),
            ("aumenta dividendo", 3.0),
            ("recompra de acoes", 2.0),
            ("eleva recomendacao", 2.5),
            ("eleva preco alvo", 2.5),
            ("dispara", 2.0),
            ("melhora", 1.5),
            ("supera", 1.5),
            ("aprova", 1.5),
            (" sobe ", 1.5),
            (" alta ", 1.5),
        )
        for kw, peso in pos_contexto:
            if kw in t_work:
                pts_pos += peso
                t_work = t_work.replace(kw, " ")

    # 4) Fatores negativos individuais sobre o texto restante
    neg_simples = (
        ("abaixo do esperado", 3.0),
        ("abaixo das estimativas", 3.0),
        ("queda forte", 3.0),
        ("prejuizo", 3.0),
        ("decepciona", 3.0),
        ("frustra", 3.0),
        ("desaba", 3.5),
        ("derrete", 3.0),
        (" despenc", 3.5),
        ("tombo", 3.0),
        ("pressiona", 2.5),
        ("pressionado", 2.5),
        ("duvidas", 2.5),
        ("duvida", 2.5),
        ("corta", 2.5),
        ("corte", 2.5),
        ("reduz", 2.0),
        ("recua", 2.0),
        ("baixa", 2.0),
        ("crise", 2.5),
        ("multa", 2.0),
        (" inadimpl", 2.5),
        (" rebaix", 2.5),
        (" queda ", 2.0),
        (" cai ", 2.0),
    )
    for kw, peso in neg_simples:
        if kw in t_work:
            pts_neg += peso
            t_work = t_work.replace(kw, " ")

    if pts_neg > 0.0:
        m_pct = re.search(r"(\d+(?:[.,]\d+)?)\s*%", t)
        pct_num = float(m_pct.group(1).replace(",", ".")) if m_pct else 0.0
        bonus_pct = 2.5 if pct_num >= 30.0 else (1.5 if pct_num >= 15.0 else (1.0 if pct_num >= 8.0 else 0.0))
        nota_neg = -(pts_neg + bonus_pct)
        if teve_composto_neg_forte or pct_num >= 10.0:
            nota_neg = min(-4.0, nota_neg)
        else:
            nota_neg = min(-2.0, nota_neg)
        pts_final = round(max(-8.0, nota_neg), 1)
        return "🔴 Atenção", "negativo", pts_final

    if pts_pos > 0.0:
        pts_final = round(min(4.0, max(1.5, pts_pos)), 1)
        return "🟢 Positivo/Provento", "positivo", pts_final

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

        titulo = it.get("titulo") or ""
        fonte = it.get("fonte", "")
        link = it.get("link", "")
        if _eh_pagina_seo_ou_irrelevante(titulo, fonte=fonte, link=link):
            continue

        fator_trim = _fator_idade_trimestre_noticia(titulo, agora_ts=agora)
        if fator_trim <= 0.0:
            continue

        qtd_30d += 1
        peso_tempo = (2.0 if ts >= limite_7d else 1.0) * fator_trim
        if ts >= limite_7d:
            qtd_7d += 1

        t_norm = _norm_txt(titulo)
        _, cat, saldo_manchete = _classificar_sentimento_noticia(titulo, fonte=fonte, link=link)
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
                    "fonte": fonte,
                    "data_str": it.get("data_str", ""),
                    "link": link,
                }
        if cat == "critico":
            cnt_critico += 1
        elif cat == "negativo" and saldo_manchete < 0.0:
            cnt_neg += 1
            if any(k in t_norm for k in ("prejuizo", "reverte lucro", "frustra", "queda de receita", "queda na receita", "corta dividendo", "corte de dividendo")):
                tem_prej_ou_frustra = True
        elif cat == "positivo" and saldo_manchete > 0.0:
            cnt_pos += 1
            cand_p = (impacto, ts)
            if cand_p > best_pos_key:
                best_pos_key = cand_p
                top_pos = {
                    "titulo": titulo,
                    "fonte": fonte,
                    "data_str": it.get("data_str", ""),
                    "link": link,
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
        news_resumo = "🔴 Prejuízo / Corte Recente" if tem_prej_ou_frustra else "🔴 Notícias Negativas"
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
def buscar_noticias_lote(tickers_tuple: tuple[str, ...], _v: int = 3) -> dict[str, list[dict]]:
    agora_ts = time.time()

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
                    if not titulo or not link or _eh_pagina_seo_ou_irrelevante(titulo, fonte=fonte, link=link):
                        continue
                    dt_obj = None
                    dt_str = ""
                    if pub:
                        try:
                            dt_obj = parsedate_to_datetime(pub)
                            dt_str = dt_obj.astimezone(BRT).strftime("%d/%m/%Y %H:%M")
                        except Exception:
                            dt_str = pub
                    tag, cat, pts_s = _classificar_sentimento_noticia(titulo, fonte=fonte, link=link)
                    fator_trim = _fator_idade_trimestre_noticia(titulo, agora_ts=agora_ts)
                    if fator_trim <= 0.0:
                        tag = "⏳ Trimestre Antigo"
                        pts_s = 0.0
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
                for el_v in body.find_all(["span", "div", "p", "small"]):
                    if sp_cot and el_v == sp_cot:
                        continue
                    t_el = " ".join(el_v.get_text(" ", strip=True).split())
                    if "%" not in t_el or len(t_el) > 24:
                        continue
                    m_vd = re.search(r"([-+]?\d{1,3}(?:,\d+)?)\s*%", t_el)
                    if not m_vd:
                        continue
                    v_num = parse_br_num(m_vd.group(1))
                    if v_num is None:
                        continue
                    ctx_cls = " ".join(el_v.get("class", [])).lower()
                    for ch_ic in el_v.find_all(["i", "svg", "span"]):
                        ctx_cls += " " + " ".join(ch_ic.get("class", [])).lower()
                    if any(k in t_el for k in ("-", "↓", "▼")) or any(k in ctx_cls for k in ("down", "danger", "red", "neg", "desval")):
                        dados["var_dia_i10"] = -abs(v_num)
                        break
                    if any(k in t_el for k in ("+", "↑", "▲")) or any(k in ctx_cls for k in ("up", "success", "green", "pos", "val")):
                        dados["var_dia_i10"] = abs(v_num)
                        break
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
            "margem bruta": "marg_bruta_i10",
            "margem liquida": "marg_liq_i10",
            "margem ebit": "marg_ebit_i10",
            "ev/ebitda": "ev_ebitda_i10",
            "ev/ebit": "ev_ebit_i10",
            "liquidez corrente": "liq_corr_i10",
            "divida bruta / patrimonio": "div_brut_patrim_i10",
            "div. bruta / patrimonio": "div_brut_patrim_i10",
            "divida liquida / ebitda": "div_liq_ebitda_i10",
            "div. liquida / ebitda": "div_liq_ebitda_i10",
            "divida liquida / patrimonio": "div_liq_pl_i10",
            "div. liquida / patrimonio": "div_liq_pl_i10",
            "div. liquida / pl": "div_liq_pl_i10",
            "cagr receitas 5 anos": "cresc_rec_5a_i10",
            "cagr receita 5 anos": "cresc_rec_5a_i10",
            "cagr lucros 5 anos": "cresc_lucro_5a_i10",
            "cagr lucro 5 anos": "cresc_lucro_5a_i10",
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

        for img_el in soup.find_all("img"):
            src_i = (img_el.get("src") or img_el.get("data-src") or "").strip()
            if "/storage/companies/" in src_i or "/companies/" in src_i:
                dados["logo_i10"] = ("https://investidor10.com.br" + src_i) if src_i.startswith("/") else src_i
                break

        return ticker, dados
    except Exception:
        return ticker, {}


@st.cache_data(ttl=900, show_spinner=False)
def buscar_investidor10_lote(tickers_tuple: tuple[str, ...], _v: int = 2) -> dict[str, dict]:
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
        df_fx = tk_fx.history(period="max", interval="1d")
        if df_fx is not None and not df_fx.empty:
            df_fx.index = pd.to_datetime(df_fx.index).tz_localize(None)
            return df_fx["Close"].dropna()
    except Exception:
        pass
    return pd.Series(dtype=float)


@st.cache_data(ttl=1800, show_spinner=False)
def buscar_dividendos_ativo(ticker: str) -> pd.Series:
    try:
        divs = yf.Ticker(f"{ticker}.SA").dividends
        if divs is not None and not divs.empty:
            divs.index = _idx_para_brt_naive(divs.index)
            return divs[divs > 0].sort_index()
    except Exception:
        pass
    return pd.Series(dtype=float)


@st.cache_data(ttl=86400, show_spinner=False)
def _descobrir_rotas_chart_i10(script_urls: tuple[str, ...], _v: int = 7) -> list[str]:
    rotas: list[str] = []
    pat = re.compile(r"""(['"`])((?:https?://[^'"`\s]+)?/(?:api/)?(?:cotacoes|quotations)/[^'"`\s]{3,180})\1""")
    pat_api = re.compile(r"""(['"`])((?:https?://[^'"`\s]+)?/api/[^'"`\s]{4,180})\1""")
    ign_js = ("jquery", "bootstrap", "popper", "chart.js", "apexcharts", "echarts", "highcharts", "sentry", "gtag", "analytics", "vendor")
    filtrados = [
        su for su in script_urls
        if not any(ig in su.lower() for ig in ign_js)
        and any(k in su.lower() for k in ("app", "main", "chart", "cotac", "quot", "acao", "acoes", "compan", "asset", "stock", "ticker", "bundle", "index", "show", "build", "pages"))
    ] or [su for su in script_urls if not any(ig in su.lower() for ig in ign_js)]

    def _ler_js(su: str):
        try:
            r = requests.get(su, headers=HEADERS, timeout=2.5)
            if r.status_code == 200:
                return [p for _, p in (pat.findall(r.text) + pat_api.findall(r.text))]
        except Exception:
            pass
        return []

    with ThreadPoolExecutor(max_workers=6) as ex_js:
        for paths in ex_js.map(_ler_js, filtrados[:14]):
            for path in paths:
                p_low = path.lower()
                if any(k in p_low for k in ("/chart", "/intraday", "/quotations")):
                    norm_p = path if (path.startswith("http") or path.startswith("/api/")) else ("/api" + path if path.startswith(("/cotacoes/", "/quotations/")) else path)
                    if norm_p not in rotas:
                        rotas.append(norm_p)
    return rotas


@st.cache_data(ttl=86400, show_spinner=False)
def _obter_meta_chart_i10(ticker: str, _v: int = 5) -> dict:
    url_pg = f"https://investidor10.com.br/acoes/{ticker.lower()}/"
    sess = requests.Session()
    sess.headers.update({
        **HEADERS,
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "pt-BR,pt;q=0.9,en-US;q=0.8",
        "Referer": "https://investidor10.com.br/",
    })
    i10_cookie = str(get_secret("INVESTIDOR10_COOKIE", "") or "").strip()
    if i10_cookie:
        sess.headers["Cookie"] = i10_cookie

    try:
        resp_pg = sess.get(url_pg, timeout=5)
        if resp_pg.status_code != 200:
            return {"erro": f"página HTTP {resp_pg.status_code}"}
        if "cf-browser-verification" in resp_pg.text or "Just a moment" in resp_pg.text[:1500]:
            return {"erro": "bloqueio Cloudflare"}

        tid = ""
        for pat_tid in (
            r'/api/cotacoes/acao/chart/(\d{1,7})/',
            r'/api/cotacoes/acao/intraday/(\d{1,7})',
            r'["\']?ticker[_-]?id["\']?\s*[:=]\s*["\']?(\d{1,7})',
            r'data-ticker-id\s*=\s*["\']?(\d{1,7})',
            r'["\']?(?:acao|stock)[_-]?id["\']?\s*[:=]\s*["\']?(\d{1,7})',
            r'["\']?company[_-]?id["\']?\s*[:=]\s*["\']?(\d{1,7})',
            r'data-id\s*=\s*["\']?(\d{1,7})',
        ):
            m_id = re.search(pat_tid, resp_pg.text, re.IGNORECASE)
            if m_id:
                tid = m_id.group(1)
                break

        rotas_desc: list[str] = []
        for _, path in re.findall(r"""(['"`])((?:https?://[^'"`\s]+)?/(?:api/)?(?:cotacoes|quotations)/[^'"`\s]{3,180}|(?:https?://[^'"`\s]+)?/api/[^'"`\s]{4,180})\1""", resp_pg.text):
            if any(k in path.lower() for k in ("/chart", "/intraday", "/quotations")):
                norm_p = path if (path.startswith("http") or path.startswith("/api/")) else ("/api" + path if path.startswith(("/cotacoes/", "/quotations/")) else path)
                if norm_p not in rotas_desc:
                    rotas_desc.append(norm_p)

        srcs = re.findall(r'<script[^>]+src=["\']([^"\']+)["\']', resp_pg.text, re.IGNORECASE)
        local_srcs = []
        for s in srcs:
            s_low = s.lower()
            if any(ig in s_low for ig in ("google", "gtm", "facebook", "clarity", "hotjar", "jquery", "bootstrap", "ads", "analytics", "cloudflare")):
                continue
            if s.startswith("/"):
                local_srcs.append("https://investidor10.com.br" + s)
            elif "investidor10.com.br" in s_low:
                local_srcs.append(s)
        if local_srcs:
            for rt_js in _descobrir_rotas_chart_i10(tuple(local_srcs)):
                if rt_js not in rotas_desc:
                    rotas_desc.append(rt_js)

        return {"tid": tid, "rotas": tuple(rotas_desc)}
    except Exception:
        return {"erro": "erro de conexão"}


def _extrair_prev_close_i10_json(js) -> float | None:
    if not isinstance(js, dict):
        return None
    for k in (
        "previous_close", "prev_close", "previous", "yesterday",
        "yesterday_close", "last_close", "close_yesterday", "anterior",
    ):
        v = js.get(k)
        if v is None:
            continue
        num = _parse_i10_num(v) if isinstance(v, str) else pd.to_numeric(v, errors="coerce")
        if pd.notna(num) and float(num) > 0:
            return float(num)
    return None

def _parse_i10_chart_json(js, eh_intraday_per: bool) -> pd.Series:
    lista_pts = None
    if isinstance(js, list):
        lista_pts = js
    elif isinstance(js, dict):
        for k_l in ("real", "data", "prices", "cotacoes", "chart", "series", "intraday", "quotes", "quotations"):
            v_l = js.get(k_l)
            if isinstance(v_l, list) and v_l:
                lista_pts = v_l
                break
            if isinstance(v_l, dict):
                for k_sub in ("real", "data", "prices", "cotacoes", "series", "intraday", "quotations"):
                    if isinstance(v_l.get(k_sub), list) and v_l[k_sub]:
                        lista_pts = v_l[k_sub]
                        break
                if lista_pts:
                    break
        if not lista_pts:
            for v_l in js.values():
                if isinstance(v_l, list) and v_l and isinstance(v_l[0], (dict, list, tuple)):
                    lista_pts = v_l
                    break
    if not lista_pts:
        return pd.Series(dtype=float)

    hoje_brt_str = datetime.now(BRT).strftime("%Y-%m-%d")
    ano_brt_int = datetime.now(BRT).year
    datas, vals = [], []
    for pt in lista_pts:
        dt_raw, vl_raw, hr_raw = None, None, None
        if isinstance(pt, dict):
            for k_dt in ("created_at", "datetime", "date_time", "date", "data", "timestamp", "dt", "time", "x", "label"):
                if pt.get(k_dt) is not None:
                    dt_raw = pt.get(k_dt)
                    break
            hr_raw = pt.get("hour") or pt.get("hora") or (pt.get("time") if dt_raw != pt.get("time") else None)
            for k_vl in ("price", "quotation", "value", "close", "cotacao", "valor", "preco", "last", "adj_price", "adjusted_price", "y"):
                if pt.get(k_vl) is not None:
                    vl_raw = pt.get(k_vl)
                    break
        elif isinstance(pt, (list, tuple)) and len(pt) >= 2:
            dt_raw, vl_raw = pt[0], pt[1]

        if dt_raw is None or vl_raw is None:
            continue
        if isinstance(dt_raw, (int, float)) and dt_raw > 1e11:
            dt_u = pd.to_datetime(dt_raw, unit="ms", utc=True, errors="coerce")
            dt_p = dt_u.tz_convert(BRT).tz_localize(None) if (pd.notna(dt_u) and (eh_intraday_per or dt_u.hour != 0 or dt_u.minute != 0)) else (dt_u.tz_localize(None) if pd.notna(dt_u) else dt_u)
        elif isinstance(dt_raw, (int, float)) and dt_raw > 1e8:
            dt_u = pd.to_datetime(dt_raw, unit="s", utc=True, errors="coerce")
            dt_p = dt_u.tz_convert(BRT).tz_localize(None) if (pd.notna(dt_u) and (eh_intraday_per or dt_u.hour != 0 or dt_u.minute != 0)) else (dt_u.tz_localize(None) if pd.notna(dt_u) else dt_u)
        else:
            dt_str_raw = str(dt_raw).strip()
            if hr_raw and len(dt_str_raw) <= 10 and ":" not in dt_str_raw:
                dt_str_raw = f"{dt_str_raw} {str(hr_raw).strip()}"
            if re.match(r"^\d{1,2}:\d{2}(?::\d{2})?$", dt_str_raw):
                dt_p = pd.to_datetime(f"{hoje_brt_str} {dt_str_raw}", errors="coerce")
            elif re.match(r"^\d{1,2}/\d{1,2}\s+\d{1,2}:\d{2}", dt_str_raw):
                p_sp = dt_str_raw.split(None, 1)
                dt_p = pd.to_datetime(f"{p_sp[0]}/{ano_brt_int} {p_sp[1]}", dayfirst=True, errors="coerce")
            else:
                dt_p = pd.to_datetime(dt_str_raw, dayfirst=bool(re.match(r"^\d{1,2}/\d{1,2}/\d{2,4}", dt_str_raw)), errors="coerce")

        if isinstance(vl_raw, str):
            vl_s = vl_raw.strip()
            if re.match(r"^[-+]?\d+,\d{3}\.\d+$", vl_s):
                vl_p = pd.to_numeric(vl_s.replace(",", ""), errors="coerce")
            elif "," in vl_s or "R$" in vl_s:
                vl_p = _parse_i10_num(vl_s)
            else:
                vl_p = pd.to_numeric(vl_s, errors="coerce")
        else:
            vl_p = pd.to_numeric(vl_raw, errors="coerce")
        if pd.notna(dt_p) and pd.notna(vl_p) and float(vl_p) > 0:
            if getattr(dt_p, "tzinfo", None) is not None:
                dt_p = dt_p.tz_convert(BRT).tz_localize(None)
            datas.append(dt_p)
            vals.append(float(vl_p))

    if not datas:
        return pd.Series(dtype=float)
    s_out = pd.Series(vals, index=pd.DatetimeIndex(datas)).sort_index()
    s_out = s_out[~s_out.index.duplicated(keep="last")]
    prev_c = _extrair_prev_close_i10_json(js)
    if prev_c is not None:
        s_out.attrs["prev_close"] = prev_c
    return s_out


def _sincronizar_cot_live_serie(s_out: pd.Series, cot_live: float | None, eh_intraday: bool) -> pd.Series:
    if s_out.empty or not cot_live or float(cot_live) <= 0.0:
        return s_out
    cot_f = float(cot_live)
    s_res = s_out.copy()
    if eh_intraday:
        s_res.iloc[-1] = cot_f
        return s_res
    agora_b = datetime.now(BRT)
    hoje_b = agora_b.date()
    ult_d_s = s_res.index[-1].date()
    if ult_d_s < hoje_b and agora_b.weekday() < 5 and agora_b.hour >= 10 and abs(float(s_res.iloc[-1]) - cot_f) > 0.001:
        prev_attr = s_res.attrs.get("prev_close")
        s_res.loc[pd.Timestamp(hoje_b)] = cot_f
        s_res = s_res.sort_index()
        if prev_attr is not None:
            s_res.attrs["prev_close"] = prev_attr
    else:
        s_res.iloc[-1] = cot_f
    return s_res

@st.cache_data(ttl=900, show_spinner=False)
def buscar_serie_investidor10_chart_com_info(
    ticker: str,
    periodo_label: str,
    ajustada: bool,
    cot_live: float | None = None,
    _v: int = 16,
) -> tuple[pd.Series, str]:
    """Tenta obter a série exata do gráfico do Investidor10 (retorna (serie, motivo))."""
    agora_brt = datetime.now(BRT)
    dias_ytd = max(1, (agora_brt.date() - date(agora_brt.year, 1, 1)).days)
    mapa_dias = {
        "1 D": 1,
        "7 D": 7,
        "30 D": 30,
        "6 M": 182,
        "YTD": dias_ytd,
        "1 A": 365,
        "5 A": 1825,
        "10 A": 3650,
        "15 A": 5475,
    }
    if periodo_label not in mapa_dias:
        return pd.Series(dtype=float), "período não suportado"

    tk_up = ticker.upper()
    tk_low = ticker.lower()
    url_pg = f"https://investidor10.com.br/acoes/{tk_low}/"

    sess = requests.Session()
    sess.headers.update({
        **HEADERS,
        "Accept": "application/json, text/plain, */*",
        "Accept-Language": "pt-BR,pt;q=0.9,en-US;q=0.8",
        "Referer": url_pg,
        "X-Requested-With": "XMLHttpRequest",
    })
    i10_cookie = str(get_secret("INVESTIDOR10_COOKIE", "") or "").strip()
    if i10_cookie:
        sess.headers["Cookie"] = i10_cookie

    dias = mapa_dias[periodo_label]
    adj_str = "true" if ajustada else "false"
    adj_int = "1" if ajustada else "0"
    mapa_cands = {
        "1 D": [1],
        "7 D": [7],
        "30 D": [30],
        "6 M": [182, 180],
        "YTD": ["ytd", dias_ytd],
        "1 A": [365, 366],
        "5 A": [1825, 1826],
        "10 A": [3650, 3652],
        "15 A": [5475, 5478],
    }
    dias_cands = mapa_cands.get(periodo_label, [dias])
    eh_intraday_per = periodo_label in ("1 D", "7 D")

    urls_diretas: list[str] = []
    if periodo_label == "1 D":
        urls_diretas.extend([
            f"https://investidor10.com.br/api/quotations/one-day/{tk_up}/",
            f"https://investidor10.com.br/api/quotations/one-day/{tk_up}",
        ])
    elif periodo_label == "7 D":
        urls_diretas.extend([
            f"https://investidor10.com.br/api/quotations/seven-days/{tk_up}/",
            f"https://investidor10.com.br/api/quotations/seven-days/{tk_up}",
            f"https://investidor10.com.br/api/cotacoes/acao/chart/{tk_low}/7/{adj_str}/real",
            f"https://investidor10.com.br/api/cotacoes/acao/chart/{tk_low}/7/{adj_int}/real",
        ])
    else:
        for d_c in dias_cands:
            d_s = str(d_c)
            urls_diretas.extend([
                f"https://investidor10.com.br/api/cotacoes/acao/chart/{tk_low}/{d_s}/{adj_str}/real",
                f"https://investidor10.com.br/api/cotacoes/acao/chart/{tk_low}/{d_s}/{adj_str}",
            ])

    diag_motivo = "indisponível"
    bloqueado_cf = False
    serie_diaria_fb = pd.Series(dtype=float)

    def _tentar_lista_urls(lista_u: list[str]) -> tuple[pd.Series, str] | None:
        nonlocal diag_motivo, bloqueado_cf, serie_diaria_fb
        vistos_u: set[str] = set()
        for url_c in [u for u in lista_u if not (u in vistos_u or vistos_u.add(u))]:
            try:
                r_c = sess.get(url_c, timeout=4.5)
                if r_c.status_code in (401, 403, 429):
                    diag_motivo = f"HTTP {r_c.status_code}"
                    bloqueado_cf = True
                    return None
                if r_c.status_code != 200:
                    diag_motivo = f"HTTP {r_c.status_code}"
                    continue
                txt_head = (r_c.text or "").lstrip()[:80].lower()
                if txt_head.startswith(("<!doctype", "<html")):
                    diag_motivo = "HTML/Cloudflare na API"
                    bloqueado_cf = True
                    continue
                js = r_c.json()
                s_out = _parse_i10_chart_json(js, eh_intraday_per=eh_intraday_per)
                if s_out.empty:
                    diag_motivo = "lista vazia na API"
                    continue

                tem_hora = any((ts.hour != 0 or ts.minute != 0) for ts in s_out.index)
                if periodo_label == "1 D":
                    s_out = s_out[s_out.index.date == s_out.index.date[-1]]
                    if not tem_hora or len(s_out) < 2:
                        if "one-day" in url_c and len(s_out) == 1 and tem_hora and cot_live and float(cot_live) > 0:
                            pass
                        else:
                            diag_motivo = "API retornou série insuficiente para 1 D"
                            continue
                    return _sincronizar_cot_live_serie(s_out, cot_live, eh_intraday=True), "Investidor10"

                if periodo_label == "7 D":
                    dias_dist_i10 = len({ts.date() for ts in s_out.index})
                    if "seven-days" in url_c and len(s_out) >= 2:
                        return _sincronizar_cot_live_serie(s_out, cot_live, eh_intraday=True), "Investidor10"
                    if tem_hora and len(s_out) >= 4 and dias_dist_i10 >= 2:
                        return _sincronizar_cot_live_serie(s_out, cot_live, eh_intraday=True), "Investidor10"
                    if serie_diaria_fb.empty and len(s_out) >= 3 and dias_dist_i10 >= 2:
                        serie_diaria_fb = s_out
                    diag_motivo = "API retornou série parcial para 7 D"
                    continue

                if len(s_out) < 2:
                    diag_motivo = f"apenas {len(s_out)} ponto(s) para {periodo_label}"
                    continue

                span_dias = int((s_out.index[-1] - s_out.index[0]).days)
                dt_ini_s = s_out.index[0].date()
                dt_fim_s = s_out.index[-1].date()
                min_spans = {"6 M": 40, "1 A": 60, "5 A": 60, "10 A": 60, "15 A": 60}
                max_spans = {"30 D": 60, "6 M": 240, "YTD": 385, "1 A": 450}
                if periodo_label in min_spans and span_dias < min_spans[periodo_label]:
                    diag_motivo = f"retornou {span_dias}d para {periodo_label}"
                    continue
                if periodo_label in max_spans and span_dias > max_spans[periodo_label]:
                    diag_motivo = f"retornou {span_dias}d para {periodo_label}"
                    continue
                if periodo_label == "YTD":
                    if dt_ini_s < date(dt_fim_s.year - 1, 12, 20):
                        diag_motivo = f"YTD iniciou em {dt_ini_s.strftime('%d/%m/%Y')}"
                        continue
                    s_sem_feriado = s_out[~((s_out.index.month == 1) & (s_out.index.day == 1))]
                    if len(s_sem_feriado) >= 2:
                        s_out = s_sem_feriado

                return _sincronizar_cot_live_serie(s_out, cot_live, eh_intraday=False), "Investidor10"
            except Exception as exc:
                diag_motivo = f"{type(exc).__name__}: {str(exc)[:35]}"
                continue
        return None

    res_direto = _tentar_lista_urls(urls_diretas)
    if res_direto is not None:
        return res_direto

    if periodo_label == "7 D" and not serie_diaria_fb.empty:
        return _sincronizar_cot_live_serie(serie_diaria_fb, cot_live, eh_intraday=False), "Investidor10"

    # Fallback interno do Investidor10 via scraping de tid/rotas caso o endpoint por ticker não tenha respondido
    if not bloqueado_cf:
        meta = _obter_meta_chart_i10(ticker)
        if not meta.get("erro"):
            tid = meta.get("tid", "")
            rotas_desc = [r for r in meta.get("rotas", ()) if ("/chart" in r.lower() or "/intraday" in r.lower() or "/quotations" in r.lower())]
            cands_meta: list[str] = []
            if tid:
                if periodo_label == "7 D":
                    cands_meta.extend([
                        f"https://investidor10.com.br/api/cotacoes/acao/chart/{tid}/7/{adj_str}/real",
                        f"https://investidor10.com.br/api/cotacoes/acao/chart/{tid}/7/{adj_int}/real",
                    ])
                elif periodo_label == "1 D":
                    cands_meta.extend([
                        f"https://investidor10.com.br/api/cotacoes/acao/intraday/{tid}",
                        f"https://investidor10.com.br/api/cotacoes/acao/chart/{tid}/1/{adj_str}/real",
                    ])
                else:
                    for d_c in dias_cands:
                        d_s = str(d_c)
                        cands_meta.extend([
                            f"https://investidor10.com.br/api/cotacoes/acao/chart/{tid}/{d_s}/{adj_str}/real",
                            f"https://investidor10.com.br/api/cotacoes/acao/chart/{tid}/{d_s}/{adj_int}/real",
                        ])
            for d_c in dias_cands[:2]:
                d_s = str(d_c)
                for r_tpl in rotas_desc:
                    url_mont = r_tpl if r_tpl.startswith("http") else ("https://investidor10.com.br" + (r_tpl if r_tpl.startswith("/") else "/" + r_tpl))
                    url_mont = re.sub(r"\$\{[^}]*(?:id|ticker)[^}]*\}|\{(?:id|ticker_id|acao_id|company_id)\}", tid or tk_low, url_mont, flags=re.IGNORECASE)
                    url_mont = re.sub(r"\$\{[^}]*(?:day|dia|period)[^}]*\}|\{(?:days|dias|period)\}", d_s, url_mont, flags=re.IGNORECASE)
                    url_mont = re.sub(r"\$\{[^}]*adj[^}]*\}|\{(?:adjusted|ajustada)\}", adj_str, url_mont, flags=re.IGNORECASE)
                    url_mont = re.sub(r"\$\{[^}]*(?:curr|moeda)[^}]*\}|\{(?:currency|moeda)\}", "real", url_mont, flags=re.IGNORECASE)
                    if "/chart/" in url_mont.lower():
                        url_mont = re.sub(
                            r"(/chart/[^/]+/)\d+((?:/(?:true|false|1|0))(?:/[^/?#]+)?)?",
                            lambda m, _ds=d_s: f"{m.group(1)}{_ds}" + (f"/{adj_str}" + ("/real" if m.group(2) and m.group(2).count("/") >= 2 else "") if m.group(2) else ""),
                            url_mont,
                            flags=re.IGNORECASE,
                        )
                    elif url_mont.rstrip("/").endswith(("/intraday", "/chart")):
                        url_mont = url_mont.rstrip("/") + (f"/{tid}" if tid else "") + (f"/{d_s}/{adj_str}/real" if "/chart" in url_mont else "")
                    if "${" not in url_mont and "{" not in url_mont:
                        tem_intra = "intraday" in url_mont.lower()
                        if (eh_intraday_per and tem_intra) or re.search(rf"(?:/|=){re.escape(d_s)}(?:/|&|$)", url_mont):
                            cands_meta.append(url_mont)

            res_meta = _tentar_lista_urls(cands_meta[:8])
            if res_meta is not None:
                return res_meta
            if periodo_label == "7 D" and not serie_diaria_fb.empty:
                return _sincronizar_cot_live_serie(serie_diaria_fb, cot_live, eh_intraday=False), "Investidor10"

    return pd.Series(dtype=float), diag_motivo

def buscar_serie_investidor10_chart(
    ticker: str,
    periodo_label: str,
    ajustada: bool,
    cot_live: float | None = None,
    _v: int = 16,
) -> pd.Series:
    return buscar_serie_investidor10_chart_com_info(ticker, periodo_label, ajustada, cot_live=cot_live)[0]


def _calc_ticks_y_i10(y_min: float, y_max: float) -> list[float]:
    span = y_max - y_min
    if span <= 0:
        return [round(y_min, 2)]
    raw_step = span / 5.0
    mag = 10 ** math.floor(math.log10(raw_step))
    cands = [1.0, 2.0, 2.5, 3.0, 5.0, 10.0]
    step = next((c * mag for c in cands if c * mag >= raw_step), 10.0 * mag)
    primeiro = math.ceil(y_min / step) * step
    ticks = [round(y_min, 2)]
    cur = primeiro
    while cur < y_max:
        if (cur - y_min) > step * 0.28 and (y_max - cur) > step * 0.28:
            ticks.append(round(cur, 2))
        cur += step
    ticks.append(round(y_max, 2))
    return sorted(set(ticks))


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
    anos_dfp = list(range(ano_atual - 4, ano_atual))

    with ThreadPoolExecutor(max_workers=6) as ex:
        futs_dfp = {a: ex.submit(carregar_cvm_doc_ano, "DFP", a) for a in anos_dfp}
        fut_itr_atual = ex.submit(carregar_cvm_doc_ano, "ITR", ano_atual)
        fut_itr_ant = ex.submit(carregar_cvm_doc_ano, "ITR", ano_atual - 1)
        dfps_lista = [(a, fut.result()) for a, fut in futs_dfp.items()]

        anuais: dict[int, dict] = {}
        for _, dados_ano in dfps_lista:
            for (c_cnpj, dt_ref), met in dados_ano.items():
                if c_cnpj == cnpj:
                    yr = int(str(dt_ref)[:4])
                    anuais[yr] = met

        if not anuais:
            return {}, None

        ult_yr = max(anuais.keys())
        if ult_yr + 1 == ano_atual:
            itr_curr = fut_itr_atual.result()
            itr_prev = fut_itr_ant.result()
        else:
            fut_curr = ex.submit(carregar_cvm_doc_ano, "ITR", ult_yr + 1)
            fut_prev = ex.submit(carregar_cvm_doc_ano, "ITR", ult_yr)
            itr_curr = fut_curr.result()
            itr_prev = fut_prev.result()

    # TTM via CVM: DFP(último_ano) + ITR_atual - ITR_mesmo_trimestre_ano_anterior
    ttm_cvm = None

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
        fi = None
        fi_pc = None
        try:
            fi = tk.fast_info
            if fi:
                cot_yf = fi.get("lastPrice") or fi.get("regularMarketPrice")
                fi_pc = fi.get("previousClose") or fi.get("regularMarketPreviousClose")
        except Exception:
            pass
        if not cot_yf:
            cot_yf = info.get("currentPrice") or info.get("regularMarketPrice")
        if not fi_pc:
            fi_pc = info.get("previousClose") or info.get("regularMarketPreviousClose")

        ifr_14 = None
        mm20 = None
        mm50 = None
        mm200 = None
        mm20_incl_pos = None
        dist_mm20_pct = None
        dist_mm50_pct = None
        dist_mm200_pct = None
        dist_max_52s_pct = None
        razao_volume = None
        var_dia_pct = None
        ret_5d_pct = None
        ret_30d_pct = None

        try:
            hist_1y = tk.history(period="1y", interval="1d", auto_adjust=False)
            if hist_1y is not None and not hist_1y.empty and "Close" in hist_1y.columns:
                close_s = hist_1y["Close"].dropna()
                if not cot_yf and not close_s.empty:
                    cot_yf = float(close_s.iloc[-1])

                px_ref = float(cot_yf) if cot_yf else (float(close_s.iloc[-1]) if not close_s.empty else None)

                if not close_s.empty and px_ref and px_ref > 0:
                    idx_brt = _idx_para_brt_naive(close_s.index)
                    agora_brt = datetime.now(BRT)
                    hoje_brt_d = agora_brt.date()
                    ult_d_h = idx_brt[-1].date()
                    c_ult = float(close_s.iloc[-1])
                    c_ant = float(close_s.iloc[-2]) if len(close_s) >= 2 else None
                    prev_ref = None
                    if ult_d_h == hoje_brt_d:
                        prev_ref = c_ant
                    elif c_ant and abs(px_ref - c_ult) / c_ult <= 0.0005 and (hoje_brt_d.weekday() >= 5 or agora_brt.hour < 10):
                        prev_ref = c_ant
                    elif fi_pc and float(fi_pc) > 0:
                        fi_pc_f = float(fi_pc)
                        if c_ant and abs(fi_pc_f - c_ant) <= max(0.03, c_ant * 0.005):
                            prev_ref = c_ant
                        elif abs(fi_pc_f - c_ult) <= max(0.03, c_ult * 0.005):
                            prev_ref = c_ult
                        else:
                            prev_ref = fi_pc_f
                    else:
                        prev_ref = c_ult
                    if prev_ref and prev_ref > 0:
                        var_dia_pct = ((px_ref / prev_ref) - 1.0) * 100.0

                    if len(close_s) >= 6 and float(close_s.iloc[-6]) > 0:
                        ret_5d_pct = ((px_ref / float(close_s.iloc[-6])) - 1.0) * 100.0
                    if len(close_s) >= 22 and float(close_s.iloc[-22]) > 0:
                        ret_30d_pct = ((px_ref / float(close_s.iloc[-22])) - 1.0) * 100.0

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
                    if px_ref and mm20 > 0:
                        dist_mm20_pct = ((px_ref / mm20) - 1.0) * 100.0
                    if len(close_s) >= 25:
                        mm20_prev = float(close_s.iloc[-25:-5].mean())
                        mm20_incl_pos = mm20 > mm20_prev
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
        fx_atual_yf = 1.0
        if fin_curr != "BRL":
            fx_s_yf = buscar_cambio_brl(fin_curr)
            if not fx_s_yf.empty:
                fx_atual_yf = float(fx_s_yf.iloc[-1])

        lpa = info.get("trailingEps") if fin_curr == "BRL" else None
        vpa = info.get("bookValue") if fin_curr == "BRL" else None
        roe_raw = info.get("returnOnEquity")
        roe = (roe_raw * 100) if roe_raw is not None else None

        mktcap_yf = info.get("marketCap")
        tot_debt_raw = info.get("totalDebt")
        tot_cash_raw = info.get("totalCash")
        ebitda_raw = info.get("ebitda")
        fcf_raw = info.get("freeCashflow")
        fco_raw = info.get("operatingCashflow")
        earn_g_raw = info.get("earningsGrowth")
        gross_m_raw = info.get("grossMargins")

        div_liq_ebitda_yf = None
        div_liq_fco_yf = None
        div_liq_mktcap_ratio = None
        fcf_yield_yf = None
        if tot_debt_raw is not None and tot_cash_raw is not None:
            div_liq_brl = (float(tot_debt_raw) - float(tot_cash_raw)) * fx_atual_yf
            if ebitda_raw is not None and float(ebitda_raw) > 0:
                ebitda_brl = float(ebitda_raw) * fx_atual_yf
                div_liq_ebitda_yf = div_liq_brl / ebitda_brl
            if fco_raw is not None and float(fco_raw) > 0:
                fco_brl = float(fco_raw) * fx_atual_yf
                div_liq_fco_yf = div_liq_brl / fco_brl
            if mktcap_yf is not None and float(mktcap_yf) > 0:
                div_liq_mktcap_ratio = div_liq_brl / float(mktcap_yf)
        if fcf_raw is not None and mktcap_yf is not None and float(mktcap_yf) > 0:
            fcf_yield_yf = ((float(fcf_raw) * fx_atual_yf) / float(mktcap_yf)) * 100.0
        cresc_lucro_yf = (float(earn_g_raw) * 100.0) if earn_g_raw is not None else None
        marg_bruta_yf = (float(gross_m_raw) * 100.0) if gross_m_raw is not None else None

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
            anos_validos_5a = [a for a in range(ano_atual - 5, ano_atual)]
            divs_5a = divs[divs.index.year.isin(anos_validos_5a)]
            if not divs_5a.empty:
                por_ano = divs_5a.groupby(divs_5a.index.year).sum()
                anos_hist = len(por_ano)
                ano_min_div = int(por_ano.index.min())
                serie_anos = sorted([float(por_ano.get(a, 0.0)) for a in anos_validos_5a if a >= ano_min_div])
                if len(serie_anos) >= 3:
                    aparados = serie_anos[1:-1]
                    dpa_med_6a = float(sum(aparados) / len(aparados))
                elif serie_anos:
                    dpa_med_6a = float(sum(serie_anos) / len(serie_anos))
                else:
                    dpa_med_6a = float(por_ano.median())

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
            "var_dia_pct": float(var_dia_pct) if var_dia_pct is not None else None,
            "ret_5d_pct": float(ret_5d_pct) if ret_5d_pct is not None else None,
            "ret_30d_pct": float(ret_30d_pct) if ret_30d_pct is not None else None,
            "lpa_yf": float(lpa) if lpa is not None else None,
            "vpa_yf": float(vpa) if vpa is not None else None,
            "roe_yf": float(roe) if roe is not None else None,
            "div_liq_ebitda_yf": float(div_liq_ebitda_yf) if div_liq_ebitda_yf is not None else None,
            "div_liq_fco_yf": float(div_liq_fco_yf) if div_liq_fco_yf is not None else None,
            "div_liq_mktcap_ratio": float(div_liq_mktcap_ratio) if div_liq_mktcap_ratio is not None else None,
            "fcf_yield_yf": float(fcf_yield_yf) if fcf_yield_yf is not None else None,
            "cresc_lucro_yf": float(cresc_lucro_yf) if cresc_lucro_yf is not None else None,
            "marg_bruta_yf": float(marg_bruta_yf) if marg_bruta_yf is not None else None,
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
            "mm20_incl_pos": mm20_incl_pos,
            "dist_mm20_pct": float(dist_mm20_pct) if dist_mm20_pct is not None else None,
            "dist_mm50_pct": float(dist_mm50_pct) if dist_mm50_pct is not None else None,
            "dist_mm200_pct": float(dist_mm200_pct) if dist_mm200_pct is not None else None,
            "dist_max_52s_pct": float(dist_max_52s_pct) if dist_max_52s_pct is not None else None,
            "razao_volume": float(razao_volume) if razao_volume is not None else None,
        }
    except Exception:
        return ticker, {}

@st.cache_data(ttl=300, show_spinner=False)
def buscar_yahoo_lote(tickers_tuple: tuple[str, ...], _v: int = 2) -> dict[str, dict]:
    if not tickers_tuple:
        return {}
    resultados = {}
    with ThreadPoolExecutor(max_workers=8) as executor:
        for ticker, dados in executor.map(_fetch_yf, tickers_tuple):
            resultados[ticker] = dados
    return resultados

@st.cache_data(ttl=600, show_spinner=False)
def buscar_ret_ibov_30d() -> float | None:
    try:
        h = yf.Ticker("^BVSP").history(period="3mo", interval="1d", auto_adjust=False)
        if h is not None and not h.empty and "Close" in h.columns:
            c = h["Close"].dropna()
            if len(c) >= 22 and float(c.iloc[-22]) > 0:
                return ((float(c.iloc[-1]) / float(c.iloc[-22])) - 1.0) * 100.0
    except Exception:
        pass
    return None


@st.cache_data(ttl=43200, show_spinner=False)
def buscar_yield_exigido_bazin() -> float:
    """Retorna Yield exigido para Bazin Dinâmico entre 6,0% e 7,5% (NTN-B 10a + 1,0%)."""
    try:
        _, selic_aa = buscar_historico_selic_bcb()
        if selic_aa and selic_aa > 0:
            ntnb_est = 0.045 + max(0.0, (float(selic_aa) - 10.0) * 0.004)
            return max(0.060, min(0.075, ntnb_est + 0.010))
    except Exception:
        pass
    return 0.065


@st.cache_data(ttl=180, show_spinner=False)
def buscar_ohlcv_preco(
    ticker: str,
    periodo_label: str,
    ajustada: bool,
    cot_live: float | None = None,
    prev_close_ref: float | None = None,
    dt_ini_ref: str | None = None,
    _v: int = 5,
) -> pd.DataFrame:
    tk = yf.Ticker(f"{ticker}.SA")
    eh_intraday = periodo_label in ("1 D", "7 D")
    agora_brt = datetime.now(BRT)
    hoje_brt_ts = pd.Timestamp(agora_brt.date())

    if periodo_label == "1 D":
        df = tk.history(period="5d", interval="5m", auto_adjust=False)
        if df is not None and not df.empty:
            df.index = _idx_para_brt_naive(df.index)
            df = df[df.index.date == df.index.date[-1]]
    elif periodo_label == "7 D":
        df = tk.history(period="1mo", interval="15m", auto_adjust=ajustada)
        if df is not None and not df.empty:
            df.index = _idx_para_brt_naive(df.index)
            ref_7d = max(df.index.max().normalize(), hoje_brt_ts)
            df = df[df.index >= (ref_7d - timedelta(days=7))]
    else:
        mapa_fetch = {"30 D": "3mo", "6 M": "1y", "YTD": "2y", "1 A": "2y", "5 A": "10y", "10 A": "max", "15 A": "max"}
        df = tk.history(period=mapa_fetch.get(periodo_label, "2y"), interval="1d", auto_adjust=ajustada)
        if df is not None and not df.empty:
            df.index = _idx_para_brt_naive(df.index)

    if df is None or df.empty or "Close" not in df.columns:
        return pd.DataFrame()

    cols_ok = [c for c in ("Open", "High", "Low", "Close", "Volume") if c in df.columns]
    df = df[cols_ok].dropna(subset=["Close"]).copy()
    if df.empty:
        return df

    px_cols = [c for c in ("Open", "High", "Low", "Close") if c in df.columns]
    prev_ref_f = float(prev_close_ref) if (prev_close_ref and float(prev_close_ref) > 0.0) else None

    # Sincroniza pregões recentes caso o endpoint diário (1d) do Yahoo esteja 1+ dia atrasado
    if not eh_intraday:
        try:
            df_5d = tk.history(period="5d", interval="15m", auto_adjust=ajustada)
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

        df = df.sort_index()
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

            pregao_hoje_ativo = (agora_brt.weekday() < 5 and agora_brt.hour >= 10)
            novo_pregao_ts = None
            if dt_fund_ts is not None and pd.notna(dt_fund_ts) and dt_fund_ts > ult_data_df:
                novo_pregao_ts = dt_fund_ts
            elif ult_data_df < hoje_brt_ts and pregao_hoje_ativo and abs(float(df["Close"].iloc[-1]) - cot_f) > 0.001:
                novo_pregao_ts = hoje_brt_ts

            if novo_pregao_ts is not None:
                if prev_ref_f is not None:
                    c_ant_yh = float(df["Close"].iloc[-1])
                    if c_ant_yh > 0 and 0.70 <= (prev_ref_f / c_ant_yh) <= 1.30 and abs(prev_ref_f - c_ant_yh) / c_ant_yh > 0.0005:
                        df[px_cols] = df[px_cols] * (prev_ref_f / c_ant_yh)
                nova_l = {"Open": cot_f, "High": cot_f, "Low": cot_f, "Close": cot_f, "Volume": 0.0}
                df.loc[novo_pregao_ts] = {k: nova_l[k] for k in df.columns}
            else:
                if prev_ref_f is not None and len(df) >= 2:
                    c_pen_yh = float(df["Close"].iloc[-2])
                    if c_pen_yh > 0 and 0.70 <= (prev_ref_f / c_pen_yh) <= 1.30 and abs(prev_ref_f - c_pen_yh) / c_pen_yh > 0.0005:
                        fator_cal = prev_ref_f / c_pen_yh
                        df.iloc[:-1, [df.columns.get_loc(c) for c in px_cols]] = df.iloc[:-1][px_cols] * fator_cal
                if abs(float(df["Close"].iloc[-1]) - cot_f) > 0.001:
                    idx_ult = df.index[-1]
                    df.loc[idx_ult, "Close"] = cot_f
                    if "High" in df.columns:
                        df.loc[idx_ult, "High"] = max(float(df.loc[idx_ult, "High"]), cot_f)
                    if "Low" in df.columns:
                        df.loc[idx_ult, "Low"] = min(float(df.loc[idx_ult, "Low"]), cot_f)

        df = df.sort_index()
        ult_d_ref = df.index.normalize().max()
        ref_corte = max(ult_d_ref, hoje_brt_ts)
        offsets_per = {
            "30 D": timedelta(days=30),
            "6 M": timedelta(days=182),
            "1 A": timedelta(days=365),
            "5 A": timedelta(days=1825),
            "10 A": timedelta(days=3650),
            "15 A": timedelta(days=5475),
        }
        if dt_ini_ref:
            dt_ref_ts = pd.to_datetime(dt_ini_ref, errors="coerce")
            if pd.notna(dt_ref_ts):
                sub_ref = df[df.index.normalize() >= dt_ref_ts.normalize()]
                if not sub_ref.empty:
                    df = sub_ref
                    return df.sort_index()
        if periodo_label == "YTD":
            df = df[df.index.normalize() >= pd.Timestamp(year=ref_corte.year, month=1, day=1)]
        elif periodo_label in offsets_per:
            dt_corte = ref_corte - offsets_per[periodo_label]
            sub_corte = df[df.index.normalize() >= dt_corte]
            if not sub_corte.empty:
                df = sub_corte
    else:
        if periodo_label == "7 D" and prev_ref_f is not None:
            dias_7d = sorted({d for d in df.index.normalize()})
            if len(dias_7d) >= 2:
                mask_ant = df.index.normalize() < dias_7d[-1]
                if mask_ant.any():
                    c_ant_7d = float(df.loc[mask_ant, "Close"].iloc[-1])
                    if c_ant_7d > 0 and 0.70 <= (prev_ref_f / c_ant_7d) <= 1.30 and abs(prev_ref_f - c_ant_7d) / c_ant_7d > 0.0005:
                        df.loc[mask_ant, px_cols] = df.loc[mask_ant, px_cols] * (prev_ref_f / c_ant_7d)

        if dt_ini_ref:
            dt_ref_ts = pd.to_datetime(dt_ini_ref, errors="coerce")
            if pd.notna(dt_ref_ts):
                sub_ref = df[df.index >= dt_ref_ts]
                if not sub_ref.empty:
                    df = sub_ref

        if cot_live and float(cot_live) > 0.0:
            cot_f = float(cot_live)
            if abs(float(df["Close"].iloc[-1]) - cot_f) > 0.001:
                idx_ult = df.index[-1]
                df.loc[idx_ult, "Close"] = cot_f
                if "High" in df.columns:
                    df.loc[idx_ult, "High"] = max(float(df.loc[idx_ult, "High"]), cot_f)
                if "Low" in df.columns:
                    df.loc[idx_ult, "Low"] = min(float(df.loc[idx_ult, "Low"]), cot_f)

    return df.sort_index()

def buscar_historico_preco(
    ticker: str,
    periodo_label: str,
    ajustada: bool,
    cot_live: float | None = None,
    prev_close_ref: float | None = None,
    dt_ini_ref: str | None = None,
) -> pd.Series:
    df = buscar_ohlcv_preco(
        ticker,
        periodo_label,
        ajustada,
        cot_live=cot_live,
        prev_close_ref=prev_close_ref,
        dt_ini_ref=dt_ini_ref,
    )
    if df is None or df.empty or "Close" not in df.columns:
        return pd.Series(dtype=float)
    return df["Close"].dropna()

@st.cache_data(ttl=300, show_spinner=False)
def buscar_prev_close_ativo(ticker: str, ref_date: date | None = None, ajustada: bool = False, _v: int = 2) -> float | None:
    try:
        tk = yf.Ticker(f"{ticker}.SA")
        h5 = tk.history(period="1mo", interval="1d", auto_adjust=ajustada)
        if h5 is not None and not h5.empty and "Close" in h5.columns:
            h5.index = _idx_para_brt_naive(h5.index)
            c5 = h5["Close"].dropna()
            if not c5.empty:
                alvo_d = ref_date or c5.index[-1].date()
                anteriores = c5[c5.index.date < alvo_d]
                if not anteriores.empty:
                    return float(anteriores.iloc[-1])
        if not ajustada:
            fi = tk.fast_info
            if fi:
                pc = fi.get("previousClose") or fi.get("regularMarketPreviousClose")
                if pc and float(pc) > 0:
                    return float(pc)
    except Exception:
        pass
    return None


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
            timeout=2.5,
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


def _calc_cdb_di_capital_mensal(meta_mensal: float, taxa_di_aa_pct: float, aliq_ir: float) -> float:
    """Calcula capital necessário em CDB 100% DI (base 30/365 dias, padrão rendafixa.github.io) para gerar meta_mensal líquida."""
    if meta_mensal <= 0.0 or taxa_di_aa_pct <= 0.0:
        return 0.0
    taxa_1m_bruta = ((1.0 + (taxa_di_aa_pct / 100.0)) ** (30.0 / 365.0)) - 1.0
    taxa_1m_liq = taxa_1m_bruta * (1.0 - aliq_ir)
    if taxa_1m_liq <= 0.0:
        return 0.0
    return meta_mensal / taxa_1m_liq


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
    with ThreadPoolExecutor(max_workers=3) as ex_hf:
        fut_det = ex_hf.submit(buscar_detalhes_fundamentus, ticker)
        fut_px = ex_hf.submit(lambda: tk.history(period="7y", interval="1d", auto_adjust=False))
        fut_info = ex_hf.submit(lambda: tk.info or {})
        det_fund = fut_det.result()
        hist_px = fut_px.result()
        info = fut_info.result()

    setor_str = det_fund.get("Setor", "").lower()
    eh_banco_seg = any(k in setor_str for k in ("intermediários financeiros", "bancos", "previdência e seguros"))

    if hist_px is not None and not hist_px.empty:
        hist_px.index = pd.to_datetime(hist_px.index).tz_localize(None)
    else:
        hist_px = pd.DataFrame()

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
        "nome_completo": "Valor Intrínseco de Benjamin Graham Ajustado pelo ROE",
        "o_que_e": "Adaptação da fórmula clássica √(22,5 × LPA × VPA_efetivo), onde VPA_efetivo = VPA × clamp(ROE / 14%, 0,40, 1,50), ajustando o valor patrimonial ao custo de capital no Brasil.",
        "como_interpretar": "Evita superestimar empresas com ROE muito baixo abaixo do custo de capital (~14%). Comprar abaixo do Graham Ajustado aumenta a margem de segurança real.",
    },
    "Preço-Teto Médio (6 anos)": {
        "categoria": "💵 Dividendos & Preços-Teto",
        "nome_completo": "Preço-Teto pela Mediana de Dividendos de 6 Anos",
        "o_que_e": "Divide a mediana anual de dividendos pagos nos últimos 6 anos por 6% (0,06), evitando que um único ano extraordinário (como picos de commodities) infle o teto.",
        "como_interpretar": "É uma régua mais estável e rigorosa que o Bazin de 12 meses, ideal para empresas cíclicas ou pagadoras tradicionais de longo prazo.",
    },
    "Preço-Teto Projetivo": {
        "categoria": "💵 Dividendos & Preços-Teto",
        "nome_completo": "Preço-Teto pelo Dividendo Projetado",
        "o_que_e": "Estima o preço máximo para 6% de yield considerando o dividendo projetado com base no lucro recente e histórico de distribuição (payout).",
        "como_interpretar": "Quando difere menos de 10% do Bazin 12m, o modelo funde ambos em um único método de Dividendos Sustentáveis para evitar dupla contagem no score.",
    },
    "Faixa de Preço do Modelo": {
        "categoria": "💵 Dividendos & Preços-Teto",
        "nome_completo": "Teto com Margem de Segurança vs Zona de Sobrepreço",
        "o_que_e": "Define duas faixas: o Teto com Margem (menor valor entre Graham Ajustado e o teto ponderado 60% Bazin Atual/Proj + 40% Mediana 6a com trava 1,25x Bazin Atual, descontado em 15%) e a Zona de Sobrepreço (para Bancos/Seguradoras: menor valor entre Graham e VPA × clamp(ROE/14%, 0,65, 1,50); para demais: menor valor entre 1,25× Graham e DY 4%).",
        "como_interpretar": "Abaixo do Teto com Margem o ativo oferece ótimo desconto; entre o Teto e o Sobrepreço está em faixa intermediária; acima da Zona de Sobrepreço dispara alerta de esticamento.",
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
    "Dívida Líquida / EBITDA & Dív/PL": {
        "categoria": "🏛️ Eficiência & Dívida",
        "nome_completo": "Alavancagem Operacional (Dív. Líquida / EBITDA) e Patrimonial",
        "o_que_e": "Mede quantos anos de geração de caixa operacional (EBITDA) seriam necessários para quitar a dívida líquida da empresa, critério principal em Utilities e Commodities.",
        "como_interpretar": "Em Commodities, < 1,5x é fortaleza balançária; em Energia/Saneamento, < 2,5x é ideal e até 3,5x aceitável. Acima de 4,5x aciona a trava de risco crítico.",
    },
    "Liquidez Corrente": {
        "categoria": "🏛️ Eficiência & Dívida",
        "nome_completo": "Ativo Circulante dividido pelo Passivo Circulante",
        "o_que_e": "Mede a capacidade da empresa de pagar suas contas e dívidas que vencem nos próximos 12 meses usando seu caixa e recebíveis de curto prazo.",
        "como_interpretar": "Acima de 1,2x já é saudável em Utilities (e 0,85x em empresas de giro rápido/commodities). Abaixo de 1,0 em geral exige atenção.",
    },
    "Score Geral": {
        "categoria": "🎯 Conceitos do Painel",
        "nome_completo": "Pontuação Combinada do Painel (0 a 100)",
        "o_que_e": "Nota principal com foco em valuation e dividendos: 70% Score Longo Prazo + 30% Score Curto Prazo, com trava de coerência (se LP < 55, Geral ≤ LP + 8).",
        "como_interpretar": "Acima de 72 pontos (com LP ≥ 70 e MS > 10%) indica forte alinhamento entre qualidade/desconto e bom momento. A trava impede que timing inflado mascare fundamentos fracos.",
    },
    "Score Longo Prazo (LP)": {
        "categoria": "🎯 Conceitos do Painel",
        "nome_completo": "Pontuação de Fundamentos por Trilha Setorial (0 a 100)",
        "o_que_e": "Avalia Valuation com métodos independentes (35 pts), Rentabilidade adaptada ao setor (30 pts), Saúde Financeira/Dív.Líq÷EBITDA/Proventos (30 pts) e Notícias LP (5 pts), em 3 trilhas: Bancos/Seguros, Utilities e Commodities/Geral.",
        "como_interpretar": "Possui trava anti-armadilha no teto de 50 pts caso haja prejuízo, alavancagem crítica (Dív.Líq/EBITDA > 4,5x ou Dív/PL > 3,0x) ou recuperação judicial.",
    },
    "Score Curto Prazo (CP)": {
        "categoria": "🎯 Conceitos do Painel",
        "nome_completo": "Pontuação de Timing Técnico & Catalisadores (0 a 100)",
        "o_que_e": "Avalia Tendência nas Médias Móveis MM20/MM50/MM200 (35 pts), IFR 14d contextualizado com trava de MM200 para evitar 'faca caindo' (30 pts), Volume Direcional 5d/60d (15 pts), Força Relativa vs IBOV 30d (10 pts) e Notícias (10 pts).",
        "como_interpretar": "Ajuda a responder se o momento do gráfico, do fluxo e das notícias é favorável sem premiar quedas severas abaixo da MM200.",
    },
    "News Score (Notícias)": {
        "categoria": "🎯 Conceitos do Painel",
        "nome_completo": "Analisador Direcional de Sentimento de Notícias (30 dias, -10 a +10)",
        "o_que_e": "Lê manchetes dos últimos 30 dias (peso 2x nos últimos 7 dias), filtrando páginas estáticas de SEO e trimestres defasados, com bloqueio de falsos positivos quando há termos negativos ('cai', 'corta', 'recua').",
        "como_interpretar": "Valores positivos (+2 a +10) indicam catalisadores como aprovação de proventos ou lucros em alta; negativos (-2 a -10) alertam sobre cortes ou quedas.",
    },
    "Vereditos do Modelo": {
        "categoria": "🎯 Conceitos do Painel",
        "nome_completo": "Selos Quantitativos de Classificação (Excelente, Bom, Regular, Indeciso, Esticado, Crítico)",
        "o_que_e": "Resumo visual automático que cruza fundamentos, descontos patrimoniais (P/VP ≤ 1,05), faixa de preço, divergência LP/CP, técnica e notícias.",
        "como_interpretar": "🟢 Excelente: Geral ≥ 72, LP ≥ 70, MS > +10% e abaixo do sobrepreço. 🔵 Bom: Desconto Patrimonial (P/VP ≤ 1,05), Qualidade (ROE ≥ 15% e MS ≥ -10%) ou Acúmulo LP. 🟠 Indeciso: |LP - CP| ≥ 20 ou notícia negativa/queda de ROE. 🟣 Esticado: IFR ≥ 70 ou Cotação > Sobrepreço. 🔴 Crítico: prejuízo, alavancagem crítica ou RJ.",
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


def html_logo_ativo(
    ticker: str,
    logo_fb: str = "",
    size: int = 36,
    radius: int = 8,
    bg_monogram: str = "rgba(59,130,246,0.22)",
) -> str:
    tk_esc = html.escape(ticker)
    src_prim = f"https://icons.brapi.dev/icons/{tk_esc}.svg"
    if logo_fb:
        fb_esc = html.escape(logo_fb, quote=True)
        onerror_js = (
            f"if(!this.dataset.triedFb){{this.dataset.triedFb='1';this.src='{fb_esc}';}}"
            "else{this.style.display='none';if(this.nextElementSibling)this.nextElementSibling.style.display='inline-flex';}"
        )
    else:
        onerror_js = "this.style.display='none';if(this.nextElementSibling)this.nextElementSibling.style.display='inline-flex';"
    fs_mono = max(9, int(size * 0.27))
    return (
        f"<span style='display:inline-flex; align-items:center; justify-content:center; width:{size}px; min-width:{size}px; max-width:{size}px; height:{size}px; min-height:{size}px; flex-shrink:0;'>"
        f"<img src='{src_prim}' alt='{tk_esc}' loading='lazy' onerror=\"{onerror_js}\" "
        f"style='width:{size}px; min-width:{size}px; max-width:{size}px; height:{size}px; min-height:{size}px; max-height:{size}px; object-fit:contain; border-radius:{radius}px; background:rgba(255,255,255,0.04); padding:2px; display:block;' />"
        f"<span style='display:none; align-items:center; justify-content:center; width:{size}px; min-width:{size}px; height:{size}px; min-height:{size}px; "
        f"border-radius:{radius}px; background:{bg_monogram}; border:1px solid rgba(148,163,184,0.35); "
        f"font-size:{fs_mono}px; font-weight:800; color:#e2e8f0; letter-spacing:0.3px;'>{html.escape(ticker[:4])}</span>"
        "</span>"
    )


def badge_veredito_html(veredito: str) -> str:
    estilos = {
        "🟢 Excelente": ("rgba(34,197,94,0.18)", "#22c55e", "rgba(34,197,94,0.45)", "🟢 Excelente"),
        "🔵 Bom (Desconto": ("rgba(59,130,246,0.18)", "#60a5fa", "rgba(59,130,246,0.45)", "🔵 Desc. Patr."),
        "🔵 Bom (Foco": ("rgba(59,130,246,0.18)", "#60a5fa", "rgba(59,130,246,0.45)", "🔵 Renda Passiva"),
        "🔵 Bom (Empresa": ("rgba(59,130,246,0.18)", "#60a5fa", "rgba(59,130,246,0.45)", "🔵 Alta Eficiência"),
        "🔵 Bom (Retorno": ("rgba(59,130,246,0.18)", "#60a5fa", "rgba(59,130,246,0.45)", "🔵 Ret. Equilibrado"),
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
    regra_sp_lbl = "P/VP(ROE/Ke) / Graham Adj · Setor Financeiro" if eh_banco_seg_fp else "DY 4% / Graham Adj 1,25x"

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
    eh_utilities = bool(r.get("eh_utilities", False))
    eh_ciclica = bool(r.get("eh_ciclica", False))
    eh_value_trap = bool(r.get("eh_value_trap", False))

    score_lp = float(r.get("score_lp") or 0.0)
    score_cp = float(r.get("score_cp") or 0.0)

    pl = r.get("pl")
    pvp = r.get("pvp")
    roe = r.get("roe")
    roic = r.get("roic")
    marg_liq = r.get("marg_liq")
    div_brut_patrim = r.get("div_brut_patrim")
    div_liq_ebitda = r.get("div_liq_ebitda")
    dy_12m = float(r.get("dy_12m") or 0.0)

    avg_ms = r.get("avg_ms")
    graham = r.get("graham")
    detalhes = r.get("detalhes_score") or {}
    n_metodos = int(detalhes.get("n_metodos") or 0)

    ifr_14 = r.get("ifr_14")
    dist_mm200 = r.get("dist_mm200_pct")
    dist_52s = r.get("dist_max_52s_pct")
    razao_vol = r.get("razao_volume")
    forca_rel = r.get("forca_rel_ibov_30d")

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
    if (not eh_banco_seg) and marg_liq is not None and marg_liq < 0:
        riscos_trap.append(f"margem líquida negativa ({fmt_num(marg_liq, 1)}%)")
    if roe is not None and roe < 0:
        riscos_trap.append(f"ROE negativo ({fmt_num(roe, 1)}%)")
    if (not eh_banco_seg) and (div_liq_ebitda is not None) and div_liq_ebitda > 4.5:
        riscos_trap.append(f"alavancagem crítica (Dív.Líq/EBITDA de {fmt_num(div_liq_ebitda)}x)")
    elif (not eh_banco_seg) and (not eh_utilities) and (div_brut_patrim is not None) and div_brut_patrim > 3.0:
        riscos_trap.append(f"endividamento elevado (Dívida/PL de {fmt_num(div_brut_patrim)}x)")
    if news_tem_rj:
        riscos_trap.append("menção recente a recuperação judicial ou falência nas notícias")

    tem_desc_patr = (pvp is not None and 0.0 < pvp <= 1.05)

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
            elif (not eh_banco_seg) and roic is not None and roic >= 9.0:
                frase_rent += f" e ROIC operacional consistente de {fmt_num(roic, 1)}%"
            elif marg_liq is not None and marg_liq >= 10.0 and not (eh_banco_seg and marg_liq == 0.0):
                frase_rent += f" e margem líquida saudável de {fmt_num(marg_liq, 1)}%"
            elif marg_liq is not None and 0.0 < marg_liq < 5.0 and not eh_banco_seg:
                frase_rent += f", porém com margem líquida mais apertada ({fmt_num(marg_liq, 1)}%)"

            if (not eh_banco_seg):
                if div_liq_ebitda is not None:
                    lim_div_ok = 2.5 if eh_utilities else 1.5
                    lim_div_mod = 3.5 if eh_utilities else 3.0
                    if div_liq_ebitda <= lim_div_ok:
                        frase_rent += f", aliada a alavancagem saudável (Dív.Líq/EBITDA de {fmt_num(div_liq_ebitda)}x)"
                    elif div_liq_ebitda <= lim_div_mod:
                        frase_rent += f" e Dív.Líq/EBITDA sob controle ({fmt_num(div_liq_ebitda)}x)"
                    else:
                        frase_rent += f", embora peça atenção à dívida (Dív.Líq/EBITDA de {fmt_num(div_liq_ebitda)}x)"
                elif div_brut_patrim is not None:
                    if div_brut_patrim <= 0.8:
                        frase_rent += ", aliada a balanço conservador e baixo endividamento"
                    elif div_brut_patrim <= 2.0:
                        frase_rent += " e dívida sob controle"
                    else:
                        frase_rent += f", embora peça atenção à alavancagem (Dív/PL de {fmt_num(div_brut_patrim)}x)"
            partes.append(frase_rent + ".")

        if avg_ms is not None and avg_ms >= 15.0:
            frase_val = f"Negocia com ampla margem de segurança consolidada de {avg_ms:+.1f}% abaixo do valor justo"
        elif avg_ms is not None and avg_ms > 0.0:
            frase_val = f"Negocia com desconto moderado ({avg_ms:+.1f}%) frente aos métodos de valuation"
        elif tem_desc_patr:
            det_p = [f"P/VP de {fmt_num(pvp)}x"]
            if graham is not None and graham > 0.0 and cot > 0.0 and cot <= float(graham):
                det_p.append(f"abaixo do Graham Ajustado (R$ {fmt_num(graham)})")
            frase_val = f"Apresenta desconto patrimonial relevante ({', '.join(det_p)})"
        elif avg_ms is not None:
            frase_val = f"Cotação negocia {abs(avg_ms):.1f}% acima do preço justo consolidado do modelo"
        else:
            frase_val = "Cobertura parcial de preços-teto pelos dados atuais"

        if n_metodos == 1:
            frase_val += " (nota: cobertura de apenas 1 método independente, aplicando trava de confiança)"
        elif n_metodos == 2:
            frase_val += " (cobertura de 2 métodos independentes)"
        partes.append(frase_val + ".")

        if dy_12m >= 6.0:
            partes.append(f"Excelente perfil para acúmulo e renda passiva com dividendos de {fmt_num(dy_12m, 1)}% em 12 meses.")
        elif dy_12m >= 3.5:
            partes.append(f"Entrega retorno intermediário em proventos (DY de {fmt_num(dy_12m, 1)}%), equilibrando renda e crescimento.")
        elif dy_12m > 0.0:
            partes.append(f"Dividend yield ainda modesto ({fmt_num(dy_12m, 1)}%), com tese mais apoiada em valor/lucro do que em renda imediata.")
        else:
            partes.append("Não distribui dividendos no momento (DY de 0%), zerando a parcela de renda na nota.")

        texto_fundamentos = " ".join(partes)
        return f"📝 **Diagnóstico Técnico & Fundamentalista:** {texto_fundamentos}\n\n{bloco_news_linhas}"

    if eh_cp:
        partes = []
        trava_ifr_mm200 = bool(detalhes.get("trava_ifr_mm200", False))
        if ifr_14 is not None:
            if trava_ifr_mm200:
                partes.append(
                    f"IFR em {fmt_num(ifr_14, 1)}, porém com trava de tendência acionada (preço >10% abaixo da MM200 sem recuperar MM20), "
                    "evitando sinal falso de compra em queda."
                )
            elif 35.0 <= ifr_14 <= 48.0:
                partes.append(
                    f"Em excelente ponto de entrada técnico: o IFR está em {fmt_num(ifr_14, 1)} "
                    "(região de respiro favorável para retomada)."
                )
            elif ifr_14 < 35.0:
                partes.append(
                    f"IFR pressionado em {fmt_num(ifr_14, 1)} (sobrevenda), sugerindo exaustão vendedora, "
                    "mas exigindo confirmação de piso."
                )
            elif ifr_14 < 70.0:
                partes.append(f"O IFR opera em {fmt_num(ifr_14, 1)}, em zona neutra/construtiva.")
            else:
                partes.append(
                    f"Alerta de esticamento no curto prazo: o IFR já marca {fmt_num(ifr_14, 1)} (sobrecompra ≥ 70), "
                    "elevando o risco de realização técnica."
                )
        else:
            partes.append("Leitura de IFR indisponível para este ativo no momento.")

        if dist_mm200 is not None:
            if dist_mm200 >= 0.0 and dist_mm200 <= 18.0:
                tr_txt = f"O preço segue {dist_mm200:+.1f}% acima da MM200 (tendência primária construtiva)"
            elif dist_mm200 > 18.0:
                tr_txt = f"O preço negocia bem esticado acima da MM200 ({dist_mm200:+.1f}%)"
            elif dist_mm200 >= -10.0:
                tr_txt = f"A cotação testa região próxima abaixo da MM200 ({dist_mm200:+.1f}%)"
            else:
                tr_txt = f"O papel segue {abs(dist_mm200):.1f}% abaixo da MM200, ainda em tendência corretiva forte"
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

        if forca_rel is not None:
            partes.append(f"Força relativa de {forca_rel:+.1f} p.p. frente ao Ibovespa em 30 dias.")

        if razao_vol is not None and razao_vol >= 1.25:
            if detalhes.get("trava_vol_dist"):
                partes.append(f"Volume elevado ({fmt_num(razao_vol, 2)}x) acompanhado de queda recente, acionando trava de distribuição.")
            else:
                partes.append(f"O volume de negócios acelerou ({fmt_num(razao_vol, 2)}x a média de 60 dias) em direção positiva.")

        texto_fundamentos = " ".join(partes)
        return f"📝 **Diagnóstico Técnico & Fundamentalista:** {texto_fundamentos}\n\n{bloco_news_linhas}"

    # Modo Geral (Combinado: 70% Longo Prazo + 30% Curto Prazo)
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
            base_lp += f" e margem de segurança consolidada de {avg_ms:+.1f}%"
        elif tem_desc_patr:
            base_lp += " e negocia com desconto patrimonial"
        elif avg_ms is not None and avg_ms < -5.0:
            base_lp += f", embora negocie {abs(avg_ms):.1f}% acima do valor justo consolidado"

    sinais_alerta_cp = []
    if ifr_14 is not None and ifr_14 >= 70.0:
        sinais_alerta_cp.append(f"IFR esticado em {fmt_num(ifr_14, 1)} (sobrecompra)")
    elif ifr_14 is not None and ifr_14 < 30.0:
        sinais_alerta_cp.append(f"IFR fortemente sobrevendido ({fmt_num(ifr_14, 1)})")
    if news_score < 0.0:
        sinais_alerta_cp.append(f"pressão de notícias negativas recentes ({news_score:+.1f} — {news_resumo})")
    if dist_mm200 is not None and dist_mm200 < -10.0:
        sinais_alerta_cp.append(f"preço {abs(dist_mm200):.1f}% abaixo da MM200")
    if abs(score_lp - score_cp) >= 20.0 and not (score_lp >= 70.0 and score_cp >= 68.0):
        sinais_alerta_cp.append(f"forte divergência entre LP ({score_lp}) e CP ({score_cp})")

    sinais_pos_cp = []
    if ifr_14 is not None and 35.0 <= ifr_14 <= 48.0 and not detalhes.get("trava_ifr_mm200"):
        sinais_pos_cp.append(f"IFR em ponto técnico atrativo ({fmt_num(ifr_14, 1)})")
    if news_score >= 2.0:
        sinais_pos_cp.append(f"notícias recentes positivas ({news_score:+.1f} — {news_resumo})")
    if razao_vol is not None and razao_vol >= 1.25 and not detalhes.get("trava_vol_dist"):
        sinais_pos_cp.append(f"volume em aceleração ({fmt_num(razao_vol, 2)}x)")

    if (not eh_value_trap) and score_lp >= 58.0 and sinais_alerta_cp:
        texto_fundamentos = f"{base_lp}, mas sinaliza cautela no curto prazo devido a {' e '.join(sinais_alerta_cp)}."
    elif sinais_pos_cp and not sinais_alerta_cp:
        texto_fundamentos = f"{base_lp}, somando bom momento no curto prazo com {' e '.join(sinais_pos_cp)}."
    elif sinais_alerta_cp:
        texto_fundamentos = f"{base_lp}, além de registrar {' e '.join(sinais_alerta_cp)}."
    elif ifr_14 is not None:
        texto_fundamentos = f"{base_lp}, mantendo quadro técnico equilibrado (IFR em {fmt_num(ifr_14, 1)}) e sentimento de mercado {news_resumo.lower()}."
    else:
        texto_fundamentos = f"{base_lp}, com sentimento de mercado {news_resumo.lower()}."

    return f"📝 **Diagnóstico Técnico & Fundamentalista:** {texto_fundamentos}\n\n{bloco_news_linhas}"

def gerar_relatorio_auditoria_ia(
    itens: list[dict],
    filtros_ctx: dict,
) -> str:
    def _f(v, casas=2, suf=""):
        if v is None or pd.isna(v):
            return "N/D"
        return f"{fmt_num(float(v), casas)}{suf}"

    def _f_rs(v):
        if v is None or pd.isna(v) or float(v) <= 0:
            return "N/D"
        return f"R$ {fmt_num(float(v))}"

    agora_s = datetime.now(BRT).strftime("%d/%m/%Y %H:%M:%S BRT")
    linhas: list[str] = [
        "# AUDITORIA COMPLETA DO MOTOR QUANTITATIVO — PAINEL VALUATION B3",
        f"Data/Hora da geração: {agora_s}",
        f"Total de ativos analisados no filtro atual: {len(itens)}",
        "",
        "## 1. FILTROS ATIVOS E CONTEXTO",
        f"- Modo de Análise ativo na interface: {filtros_ctx.get('modo_ativo', 'Geral')}",
        f"- Listas rápidas: {', '.join(filtros_ctx.get('listas') or []) or 'Nenhuma (Todas)'}",
        f"- Setores específicos: {', '.join(filtros_ctx.get('setores') or []) or 'Todos'}",
        f"- Liquidez mínima (2m): {filtros_ctx.get('liq', 'N/D')}",
        f"- Filtro de vereditos: {', '.join(filtros_ctx.get('vereditos') or []) or 'Todos'}",
        f"- Busca código/tabela: {filtros_ctx.get('busca') or 'Nenhuma'}",
        "",
        "## 2. METODOLOGIA, FÓRMULAS E PESOS DO SCORE",
        "- Score Geral (0–100) = 0,70 × Score_LP + 0,30 × Score_CP (com trava: se LP < 55, Geral ≤ LP + 8).",
        "- Score Longo Prazo (LP, 0–100) por 3 trilhas setoriais:",
        "  • Valuation (até 35 pts): MS Consolidada pela mediana dos métodos independentes (Dividendos Sustentáveis com fusão Bazin/Proj se diff < 10%, Graham Ajustado por ROE/Ke=14% e Múltiplo Justo setorial) com piso -100% [até 20 pts × Fator de Confiança] + Múltiplos [10 pts] + Dividendos/FCF [5 pts].",
        "  • Rentabilidade (até 30 pts): Bancos (ROE 20 com 14%→13 pts + Cresc/Estab. Lucro 5a 10); Utilities (ROE 10, ROIC 10, Marg. Líq 5, Marg. EBIT 5); Commodities (ROIC 14, ROE 8, Marg. Líq 4, Marg. EBIT 4); Geral (ROE 12, ROIC 10, Marg. Líq 5, Marg. EBIT 3).",
        "  • Saúde & Crescimento (até 30 pts): Bancos (Proventos Consecutivos 6a 10, Cresc. 5a 10, P/VP Justo vs ROE 10); Utilities (Dív.Líq/EBITDA 14, Liq. Corr 4, Cresc. 6, Estab. EBIT/ROIC 6); Commodities (Dív.Líq/EBITDA 15, Liq. Corr >=0,85x 5, Cresc. Suavizado 5, Solidez/FCF 5); Geral (Dív.Líq/EBITDA ou Dív/PL 12, Liq. Corr 8, Cresc. 10).",
        "  • Notícias LP (até 5 pts): News Score (-10 a +10) normalizado para 0–5 (com blacklist SEO e filtro de trimestre defasado).",
        "  • Trava Anti-Armadilha: limita LP a 50 pts se Marg. Líq < 0 (não-bancos), ROE < 0, Dív.Líq/EBITDA > 4,5x (ou Dív/PL > 3,0x não-utilities) ou RJ/falência.",
        "- Score Curto Prazo (CP, 0–100):",
        "  • Médias Móveis MM20/MM50/MM200 (35 pts) + IFR 14d com trava máx 15 pts se Cotação < 0,90×MM200 sem recuperar MM20 inclinada (30 pts) + Volume Direcional 5d/60d (15 pts) + Força Relativa vs IBOV 30d (10 pts) + News Score 30d (10 pts).",
        "- Faixa de Preço do Modelo: Teto com Margem = min(Graham Adj, PT_div_ref × 0,85) com PT_div_ref = 0,60×PT_Bazin_Atual_ou_Proj + 0,40×PT_Mediana_6a (<=1,25×PT_Bazin_Atual); Sobrepreço = Bancos min(Graham Adj, VPA × clamp(ROE/14%, 0,65, 1,50)); demais min(1,25×Graham Adj, DPA/0,04).",
        "- Vereditos: Crítico -> Esticado (IFR>=70 ou Cotação > Sobrepreço) -> Indeciso (|LP-CP|>=20, News<=-2,5, lucro sólido com news<0, ou ROE<8% com histórico) -> Excelente (Geral>=72, LP>=70, MS>10% e Cotação<=Sobrepreço) -> Bom (Desc. Patr. se P/VP<=1,05 / Qualidade / Acúmulo LP) -> Regular.",
        "",
    ]

    if not itens:
        linhas.append("Nenhum ativo encontrado no filtro atual.")
        return "\n".join(linhas)

    rank_geral = sorted(itens, key=lambda x: x.get("score_geral", 0.0), reverse=True)
    rank_lp = sorted(itens, key=lambda x: x.get("score_lp", 0.0), reverse=True)
    rank_cp = sorted(itens, key=lambda x: x.get("score_cp", 0.0), reverse=True)
    pos_g_map = {r["ticker"]: i for i, r in enumerate(rank_geral, 1)}
    pos_lp_map = {r["ticker"]: i for i, r in enumerate(rank_lp, 1)}
    pos_cp_map = {r["ticker"]: i for i, r in enumerate(rank_cp, 1)}

    linhas.append("## 3. COMPARATIVO DOS 3 MÓDULOS DE RANKING")
    linhas.append("### 3.1 Ranking Geral (70% LP + 30% CP)")
    for i, r in enumerate(rank_geral, 1):
        linhas.append(f"{i}º {r['ticker']} ({r['nome']}) | Geral: {r['score_geral']} (LP: {r['score_lp']} | CP: {r['score_cp']} | News: {r.get('news_score', 0):+.1f}) | {r.get('veredito', '')}")
    linhas.append("")
    linhas.append("### 3.2 Ranking Longo Prazo (Fundamentos & Dividendos)")
    for i, r in enumerate(rank_lp, 1):
        linhas.append(f"{i}º {r['ticker']} ({r['nome']}) | LP: {r['score_lp']} (Geral: {r['score_geral']} | CP: {r['score_cp']}) | {r.get('veredito', '')}")
    linhas.append("")
    linhas.append("### 3.3 Ranking Curto Prazo (Timing & Catalisadores)")
    for i, r in enumerate(rank_cp, 1):
        linhas.append(f"{i}º {r['ticker']} ({r['nome']}) | CP: {r['score_cp']} (Geral: {r['score_geral']} | LP: {r['score_lp']}) | IFR: {_f(r.get('ifr_14'), 1)} | News: {r.get('news_score', 0):+.1f}")
    linhas.append("")
    linhas.append("## 4. ANÁLISE DETALHADA POR ATIVO (TODOS OS MÓDULOS)")

    for r in rank_geral:
        tk = r["ticker"]
        det = r.get("detalhes_score") or {}
        dfp = _dados_faixa_preco(r)
        j_g = re.sub(r"<[^>]+>", "", gerar_justificativa_detalhada(r, "score_geral").split("\n\n")[0])
        j_lp = re.sub(r"<[^>]+>", "", gerar_justificativa_detalhada(r, "score_lp").split("\n\n")[0])
        j_cp = re.sub(r"<[^>]+>", "", gerar_justificativa_detalhada(r, "score_cp").split("\n\n")[0])
        top_p = r.get("top_noticia_pos")
        top_n = r.get("top_noticia_neg")
        trilha_lbl = det.get("trilha", "Geral")
        linhas.extend([
            f"### {tk} — {r.get('nome', tk)} | Setor: {r.get('setor_nome') or 'N/D'} | Trilha: {trilha_lbl}",
            f"- Posições: Geral {pos_g_map[tk]}º | Longo Prazo {pos_lp_map[tk]}º | Curto Prazo {pos_cp_map[tk]}º",
            f"- Cotação: R$ {fmt_num(float(r.get('cotacao') or 0.0))} | Var. Dia: {_f(r.get('var_dia_pct'), 2, '%')} | Liquidez 2m: R$ {fmt_bi_mi(r.get('liq_2m'))}",
            f"- Scores: Geral={r['score_geral']}/100 | LP={r['score_lp']}/100 [Val={det.get('pts_val_lp', 0)}/35 (conf={det.get('fator_confianca', 1)}, métodos={det.get('n_metodos', 0)}), Rent={det.get('pts_rent_lp', 0)}/30, Saúde={det.get('pts_saude_lp', 0)}/30, NewsLP={det.get('pts_news_lp', 0)}/5, ValueTrap={r.get('eh_value_trap', False)}] | CP={r['score_cp']}/100 [Médias={det.get('pts_medias_cp', 0)}/35, IFR={det.get('pts_ifr_cp', 0)}/30, Vol={det.get('pts_vol_cp', 0)}/15, IBOV={det.get('pts_ibov_cp', 0)}/10, NewsCP={det.get('pts_news_cp', 0)}/10]",
            f"- Veredito Quantitativo: {r.get('veredito', '')}",
            f"- Motivos do Score: {'; '.join(r.get('motivos') or []) or 'Nenhum'}",
            f"- Fundamentalistas: P/L={_f(r.get('pl'))} | P/VP={_f(r.get('pvp'))} | ROE={_f(r.get('roe'), 1, '%')} | ROIC={_f(r.get('roic'), 1, '%')} | Marg.Líq={_f(r.get('marg_liq'), 1, '%')} | Marg.EBIT={_f(r.get('marg_ebit'), 1, '%')} | EV/EBITDA={_f(r.get('ev_ebitda'))} | Liq.Corr={_f(r.get('liq_corr'))} | Dív.Líq/EBITDA={_f(r.get('div_liq_ebitda'))} | Dív.Brut/PL={_f(r.get('div_brut_patrim'))} | Cresc.Rec.5a={_f(r.get('cresc_rec_5a'), 1, '%')} | LPA={_f_rs(r.get('lpa'))} | VPA={_f_rs(r.get('vpa'))}",
            f"- Dividendos & Valuation: DY 12m={_f(r.get('dy_12m'), 2, '%')} | DPA 12m={_f_rs(r.get('dpa_12m'))} | DPA Mediana 6a={_f_rs(r.get('dpa_med_6a'))} ({r.get('anos_hist', 0)}a, {r.get('anos_divs_consec', 0)} consec.) | DPA Proj={_f_rs(r.get('dpa_proj'))} | PT Mediana 6a={_f_rs(r.get('pt_med'))} | PT Proj={_f_rs(r.get('pt_proj'))} | PT Bazin={_f_rs(r.get('pt_bazin'))} | Graham Adj={_f_rs(r.get('graham'))} | PT Múlt. Justo={_f_rs(r.get('pt_mult_justo'))} | PT Justo Cons.={_f_rs(r.get('pt_justo_consolidado'))} | MS Cons.={_f(r.get('avg_ms'), 1, '%')}",
            f"- Faixa de Preço do Modelo ({dfp['regra_sp_lbl']}): Desconto={dfp['z_desc']} | Neutra={dfp['z_neutro']} | Sobrepreço={dfp['z_sobre']} | Veredito={re.sub(r'[*]+', '', dfp['veredito_px'])}",
            f"- Técnicos: IFR(14)={_f(r.get('ifr_14'), 1)} | MM20={_f_rs(r.get('mm20'))} | MM50={_f_rs(r.get('mm50'))} (dist {_f(r.get('dist_mm50_pct'), 1, '%')}) | MM200={_f_rs(r.get('mm200'))} (dist {_f(r.get('dist_mm200_pct'), 1, '%')}) | Dist.Máx 52s={_f(r.get('dist_max_52s_pct'), 1, '%')} | Razão Vol 5d/60d={_f(r.get('razao_volume'), 2, 'x')} | Força Rel. IBOV 30d={_f(r.get('forca_rel_ibov_30d'), 1, ' p.p.')}",
            f"- Notícias (30d): Score={r.get('news_score', 0):+.1f} | Resumo={r.get('news_resumo', '')} | Qtd 7d={r.get('news_qtd_7d', 0)} / 30d={r.get('news_qtd_30d', 0)} | RJ={r.get('news_tem_rj', False)}"
            + (f" | Top Positiva: '{top_p.get('titulo', '')}' ({top_p.get('fonte', '')}, {top_p.get('data_str', '')})" if top_p else "")
            + (f" | Top Negativa: '{top_n.get('titulo', '')}' ({top_n.get('fonte', '')}, {top_n.get('data_str', '')})" if top_n else ""),
            f"- Diagnóstico Módulo Geral: {j_g}",
            f"- Diagnóstico Módulo Longo Prazo: {j_lp}",
            f"- Diagnóstico Módulo Curto Prazo: {j_cp}",
            "",
        ])

    linhas.extend([
        "## 5. PEDIDO DE AUDITORIA PARA A IA",
        "Com base nos dados, sub-scores, fórmulas, pesos e rankings acima:",
        "1. A pontuação de Score Geral, Longo Prazo e Curto Prazo e o ordenamento dos ativos estão coerentes com os fundamentos e momento técnico?",
        "2. Há algum viés, distorção por setor (ex.: bancos, elétricas, commodities), dado faltante penalizando injustamente ou regra de veredito que deveria ser calibrada?",
        "3. Quais melhorias práticas de cálculo/pesos você recomenda?",
    ])
    return "\n".join(linhas)


def render_grafico_e_tabela_ativo(
    ticker: str,
    nome: str = "",
    base_ativo: dict | None = None,
    key_prefix: str = "raiox",
    modo_score_chave: str = "score_geral",
    mostrar_cabecalho: bool = True,
    expandir_padrao: bool = True,
):
    logo_fb_rx = (base_ativo or {}).get("logo_i10", "")
    if mostrar_cabecalho:
        c_tit, c_fav = st.columns([4, 1.3], vertical_alignment="center")
        eh_fav = ticker in st.session_state["favoritos"]
        with c_tit:
            logo_top_rx = html_logo_ativo(ticker, logo_fb_rx, size=28, radius=6)
            sub_nm = f" — {html.escape(nome)}" if (nome and nome != ticker) else ""
            st.markdown(
                f"<div style='display:flex; align-items:center; gap:9px; font-size:22px; font-weight:700; margin:6px 0;'>"
                f"{logo_top_rx}<span>COTAÇÃO {html.escape(ticker)}{sub_nm}</span></div>",
                unsafe_allow_html=True,
            )
        with c_fav:
            lbl_fav = "★ Remover dos Favoritos" if eh_fav else "⭐ Adicionar aos Favoritos"
            if st.button(lbl_fav, key=f"{key_prefix}_favbtn_{ticker}", use_container_width=True):
                toggle_favorito(ticker)
                st.rerun(scope="app")

    serie = pd.Series(dtype=float)
    opcoes_per_i10 = ["1 D", "7 D", "30 D", "6 M", "YTD", "1 A", "5 A", "10 A", "15 A"]
    k_candles = f"{key_prefix}_candles_i10_{ticker}"
    k_marcos = f"{key_prefix}_marcos_i10_{ticker}"
    k_provs = f"{key_prefix}_provs_i10_{ticker}"
    k_comp_ativos = f"{key_prefix}_comp_i10_{ticker}"
    k_comp_ibov = f"{key_prefix}_comp_ibov_i10_{ticker}"
    k_comp_selic = f"{key_prefix}_comp_selic_i10_{ticker}"
    if k_candles not in st.session_state:
        st.session_state[k_candles] = False
    if k_marcos not in st.session_state:
        st.session_state[k_marcos] = False
    if k_provs not in st.session_state:
        st.session_state[k_provs] = False

    st.markdown(
        "<span class='raiox-blocks-host' style='display:none;'></span>"
        "<style>"
        "div[data-testid='stElementContainer']:has(.raiox-blocks-host),"
        "div.element-container:has(.raiox-blocks-host),"
        "div[data-testid='stElementContainer']:has(.raiox-indent-host),"
        "div.element-container:has(.raiox-indent-host){"
        "display:none!important;margin:0!important;padding:0!important;height:0!important;}"
        "div[data-testid='stVerticalBlock']:has(> div .raiox-blocks-host),"
        "div[data-testid='stVerticalBlock']:has(> div > div .raiox-blocks-host){"
        "gap:0!important;margin:0!important;padding:0!important;}"
        "div[data-testid='stVerticalBlock']:has(> div .raiox-blocks-host) > div[data-testid='stElementContainer'],"
        "div[data-testid='stVerticalBlock']:has(> div > div .raiox-blocks-host) > div.element-container{"
        "margin:0!important;padding:0!important;}"
        "div[data-testid='stVerticalBlock']:has(> div .raiox-blocks-host) > div[data-testid='stExpander'],"
        "div[data-testid='stVerticalBlock']:has(> div > div .raiox-blocks-host) > div > div[data-testid='stExpander']{"
        "border:1px solid rgba(59,130,246,0.42)!important;"
        "border-left:4px solid #3b82f6!important;"
        "border-radius:0!important;"
        "margin-top:-1px!important;"
        "margin-bottom:0!important;"
        "overflow:hidden;}"
        "div[data-testid='stVerticalBlock']:has(> div .raiox-indent-host) > div[data-testid='stExpander'],"
        "div[data-testid='stVerticalBlock']:has(> div > div .raiox-indent-host) > div > div[data-testid='stExpander']{"
        "margin-left:16px!important;width:calc(100% - 16px)!important;}"
        "div[data-testid='stVerticalBlock']:has(> div .raiox-blocks-host) > div[data-testid='stExpander'] details > summary,"
        "div[data-testid='stVerticalBlock']:has(> div > div .raiox-blocks-host) > div > div[data-testid='stExpander'] details > summary{"
        "background:linear-gradient(90deg, rgba(59,130,246,0.22) 0%, rgba(59,130,246,0.08) 100%)!important;"
        "font-weight:600!important;}"
        "div[data-testid='stVerticalBlock']:has(> div .raiox-blocks-host) > div[data-testid='stExpander'] details > summary:hover,"
        "div[data-testid='stVerticalBlock']:has(> div > div .raiox-blocks-host) > div > div[data-testid='stExpander'] details > summary:hover{"
        "background:linear-gradient(90deg, rgba(59,130,246,0.32) 0%, rgba(59,130,246,0.14) 100%)!important;}"
        "</style>",
        unsafe_allow_html=True,
    )

    k_chart_open = f"{key_prefix}_chart_open_{ticker}"

    def _marcar_chart_aberto():
        st.session_state[k_chart_open] = True

    @st.fragment
    def _frag_cotacao_sim():
        c_i10_hdr1, c_i10_hdr2, c_i10_hdr3 = st.columns([1.3, 2.7, 0.35], vertical_alignment="center")
        with c_i10_hdr1:
            logo_hdr_g = html_logo_ativo(ticker, logo_fb_rx, size=26, radius=6)
            st.markdown(
                f"<div style='display:flex; align-items:center; gap:9px; font-weight:700; font-size:15px; white-space:nowrap;'>"
                f"{logo_hdr_g}<span>COTAÇÃO {html.escape(ticker)}</span></div>",
                unsafe_allow_html=True,
            )
        with c_i10_hdr2:
            if hasattr(st, "segmented_control"):
                periodo = st.segmented_control(
                    "Período:",
                    options=opcoes_per_i10,
                    default="1 A",
                    label_visibility="collapsed",
                    key=f"{key_prefix}_per_seg_{ticker}",
                    on_change=_marcar_chart_aberto,
                    width="stretch",
                )
                if not periodo:
                    periodo = "1 A"
            else:
                periodo = st.radio(
                    "Período:",
                    opcoes_per_i10,
                    index=5,
                    horizontal=True,
                    label_visibility="collapsed",
                    key=f"{key_prefix}_per_{ticker}",
                    on_change=_marcar_chart_aberto,
                )
        with c_i10_hdr3:
            dt_custom_ini = None
            dt_custom_fim = None
            if hasattr(st, "popover"):
                with st.popover("📅", help="Filtrar intervalo personalizado de datas"):
                    usar_custom_dt = st.checkbox("Usar datas personalizadas", key=f"{key_prefix}_use_dt_{ticker}", on_change=_marcar_chart_aberto)
                    if usar_custom_dt:
                        hoje_d_i10 = datetime.now(BRT).date()
                        dt_custom_ini = st.date_input("De:", value=hoje_d_i10 - timedelta(days=365), format="DD/MM/YYYY", key=f"{key_prefix}_dt_i_{ticker}")
                        dt_custom_fim = st.date_input("Até:", value=hoje_d_i10, format="DD/MM/YYYY", key=f"{key_prefix}_dt_f_{ticker}")

        cot_ref_live = float(base_ativo.get("cotacao") or 0.0) if base_ativo else None
        var_dia_live = base_ativo.get("var_dia_pct") if base_ativo else None
        prev_close_live = None
        if cot_ref_live and cot_ref_live > 0.0 and var_dia_live is not None:
            denom_vd = 1.0 + (float(var_dia_live) / 100.0)
            if denom_vd > 0.1:
                prev_close_live = cot_ref_live / denom_vd
        c_tb_px, c_tb_b1, c_tb_b2, c_tb_b3, c_tb_moeda, c_tb_tipo, c_tb_cmp = st.columns(
            [1.95, 0.42, 0.42, 0.42, 0.85, 1.25, 0.95],
            vertical_alignment="center",
        )
        with c_tb_b1:
            if st.button("🎯", key=f"{key_prefix}_btn_m_{ticker}", type="primary" if st.session_state[k_marcos] else "secondary", help="Mostrar/ocultar Máxima, Mínima do período e seu Preço Médio", use_container_width=True):
                st.session_state[k_chart_open] = True
                st.session_state[k_marcos] = not st.session_state[k_marcos]
                st.rerun()
        with c_tb_b2:
            if st.button("🕯️", key=f"{key_prefix}_btn_c_{ticker}", type="primary" if st.session_state[k_candles] else "secondary", help="Alternar entre Área e Candles (DEXTools)", use_container_width=True):
                st.session_state[k_chart_open] = True
                st.session_state[k_candles] = not st.session_state[k_candles]
                st.rerun()
        with c_tb_b3:
            if st.button("🐷", key=f"{key_prefix}_btn_p_{ticker}", type="primary" if st.session_state[k_provs] else "secondary", help="Mostrar/ocultar dividendos e JCP pagos no período", use_container_width=True):
                st.session_state[k_chart_open] = True
                st.session_state[k_provs] = not st.session_state[k_provs]
                st.rerun()
        with c_tb_moeda:
            moeda_graf = st.selectbox("Moeda:", ["Real", "Dólar"], index=0, label_visibility="collapsed", key=f"{key_prefix}_moeda_{ticker}", on_change=_marcar_chart_aberto)
        with c_tb_tipo:
            tipo_cot = st.selectbox("Tipo:", ["Cotação ajustada", "Cotação simples"], index=0, label_visibility="collapsed", key=f"{key_prefix}_tipo_{ticker}", on_change=_marcar_chart_aberto)
        with c_tb_cmp:
            if hasattr(st, "popover"):
                with st.popover("⇄ Comparar", use_container_width=True):
                    st.checkbox("IBOV (Ibovespa)", key=k_comp_ibov)
                    st.checkbox("Tesouro Selic", key=k_comp_selic)
                    opcs_cmp_i10 = sorted({t_c for t_c in ([ticker] + st.session_state.get("favoritos", []) + ["BBAS3", "BBDC3", "ITUB4", "PETR4", "VALE3", "WEGE3", "TAEE11", "SANB11"]) if t_c != ticker})
                    st.multiselect("Outros ativos B3:", options=opcs_cmp_i10, key=k_comp_ativos, placeholder="Ex: PETR4, ITUB4")

        ajustada = tipo_cot == "Cotação ajustada"
        eh_candles_req = bool(st.session_state[k_candles])
        usar_custom_range = (dt_custom_ini is not None and dt_custom_fim is not None and dt_custom_ini < dt_custom_fim)

        usou_i10_graf = False
        diag_i10_graf = ""
        ajustada_alt = not ajustada
        df_ohlcv = pd.DataFrame()
        serie_alt = pd.Series(dtype=float)

        if usar_custom_range:
            with ThreadPoolExecutor(max_workers=2) as ex_gc:
                f_main = ex_gc.submit(buscar_ohlcv_preco, ticker, "15 A", ajustada, cot_ref_live, prev_close_live)
                f_alt = ex_gc.submit(buscar_ohlcv_preco, ticker, "15 A", ajustada_alt, cot_ref_live, prev_close_live)
                df_ohlcv = f_main.result()
                df_alt = f_alt.result()
            if df_ohlcv is not None and not df_ohlcv.empty:
                df_ohlcv = df_ohlcv[(df_ohlcv.index.date >= dt_custom_ini) & (df_ohlcv.index.date <= dt_custom_fim)]
            serie = df_ohlcv["Close"].dropna() if (df_ohlcv is not None and not df_ohlcv.empty and "Close" in df_ohlcv.columns) else pd.Series(dtype=float)
            if df_alt is not None and not df_alt.empty and "Close" in df_alt.columns:
                df_alt = df_alt[(df_alt.index.date >= dt_custom_ini) & (df_alt.index.date <= dt_custom_fim)]
                serie_alt = df_alt["Close"].dropna()
            lbl_per_exib = f"{dt_custom_ini.strftime('%d/%m/%y')}–{dt_custom_fim.strftime('%d/%m/%y')}"
        else:
            lbl_per_exib = periodo
            if not eh_candles_req:
                with ThreadPoolExecutor(max_workers=2) as ex_g:
                    f_i10 = ex_g.submit(buscar_serie_investidor10_chart_com_info, ticker, periodo, ajustada, cot_ref_live)
                    f_i10_alt = ex_g.submit(buscar_serie_investidor10_chart, ticker, periodo, ajustada_alt, cot_ref_live) if periodo != "1 D" else None
                    serie_i10_c, diag_i10_graf = f_i10.result()
                    if f_i10_alt is not None:
                        serie_alt = f_i10_alt.result()

                if not serie_i10_c.empty:
                    serie = serie_i10_c
                    usou_i10_graf = True
                else:
                    dt_ini_fb = serie_alt.index[0].strftime("%Y-%m-%d") if not serie_alt.empty else None
                    df_ohlcv = buscar_ohlcv_preco(
                        ticker,
                        periodo,
                        ajustada,
                        cot_live=cot_ref_live,
                        prev_close_ref=prev_close_live,
                        dt_ini_ref=dt_ini_fb,
                    )
                    serie = df_ohlcv["Close"].dropna() if (df_ohlcv is not None and not df_ohlcv.empty and "Close" in df_ohlcv.columns) else pd.Series(dtype=float)

                if not serie.empty and periodo != "1 D" and serie_alt.empty:
                    serie_alt = buscar_historico_preco(
                        ticker,
                        periodo,
                        ajustada_alt,
                        cot_live=cot_ref_live,
                        prev_close_ref=prev_close_live,
                        dt_ini_ref=serie.index[0].strftime("%Y-%m-%d"),
                    )
            else:
                with ThreadPoolExecutor(max_workers=2) as ex_c:
                    f_yh_c = ex_c.submit(buscar_ohlcv_preco, ticker, periodo, ajustada, cot_ref_live, prev_close_live)
                    f_alt_c = ex_c.submit(buscar_serie_investidor10_chart, ticker, periodo, ajustada_alt, cot_ref_live) if periodo != "1 D" else None
                    df_ohlcv = f_yh_c.result()
                    if f_alt_c is not None:
                        serie_alt = f_alt_c.result()
                serie = df_ohlcv["Close"].dropna() if (df_ohlcv is not None and not df_ohlcv.empty and "Close" in df_ohlcv.columns) else pd.Series(dtype=float)
                if not serie.empty and periodo != "1 D" and serie_alt.empty:
                    serie_alt = buscar_historico_preco(
                        ticker,
                        periodo,
                        ajustada_alt,
                        cot_live=cot_ref_live,
                        prev_close_ref=prev_close_live,
                        dt_ini_ref=serie.index[0].strftime("%Y-%m-%d"),
                    )

            if not serie.empty and not serie_alt.empty and serie_alt.index[0].normalize() < serie.index[0].normalize():
                sub_alt = serie_alt[serie_alt.index.normalize() >= serie.index[0].normalize()]
                if not sub_alt.empty:
                    serie_alt = sub_alt

        simb_moeda = "R$"
        if moeda_graf == "Dólar" and not serie.empty:
            fx_usd = buscar_cambio_brl("USD")
            if not fx_usd.empty:
                simb_moeda = "US$"
                fx_alinhado = fx_usd.reindex(serie.index.normalize(), method="ffill").bfill()
                fx_vals = pd.Series(fx_alinhado.values, index=serie.index)
                serie = (serie / fx_vals).dropna()
                if not serie_alt.empty:
                    fx_alt = fx_usd.reindex(serie_alt.index.normalize(), method="ffill").bfill()
                    serie_alt = (serie_alt / pd.Series(fx_alt.values, index=serie_alt.index)).dropna()
                if not df_ohlcv.empty:
                    df_ohlcv = df_ohlcv.loc[serie.index].copy()
                    fx_df = fx_usd.reindex(df_ohlcv.index.normalize(), method="ffill").bfill()
                    for col_px in ("Open", "High", "Low", "Close"):
                        if col_px in df_ohlcv.columns:
                            df_ohlcv[col_px] = df_ohlcv[col_px] / fx_df.values

        comp_ibov_on = bool(st.session_state.get(k_comp_ibov, False))
        comp_selic_on = bool(st.session_state.get(k_comp_selic, False))
        comp_tks = list(st.session_state.get(k_comp_ativos, []))
        modo_comparar = (comp_ibov_on or comp_selic_on or len(comp_tks) > 0) and not serie.empty

        if serie.empty:
            with c_tb_px:
                st.markdown(f"<div style='font-size:11px; opacity:0.65;'>BVMF • {ticker}</div><strong>Indisponível</strong>", unsafe_allow_html=True)
            st.warning(f"Não foi possível carregar o gráfico de {ticker} para o período {lbl_per_exib}.")
        else:
            p_ini, p_fim = float(serie.iloc[0]), float(serie.iloc[-1])
            p_ref_var = p_ini
            if not usar_custom_range and periodo == "1 D" and moeda_graf == "Real":
                prev_attr_1d = serie.attrs.get("prev_close") if hasattr(serie, "attrs") else None
                if prev_attr_1d and float(prev_attr_1d) > 0:
                    p_ref_var = float(prev_attr_1d)
                elif prev_close_live and prev_close_live > 0:
                    p_ref_var = float(prev_close_live)
                else:
                    prev_c_1d = buscar_prev_close_ativo(ticker, serie.index[-1].date(), ajustada=False)
                    if prev_c_1d and prev_c_1d > 0:
                        p_ref_var = prev_c_1d
            var_pct = ((p_fim - p_ref_var) / p_ref_var) * 100.0 if p_ref_var > 0 else 0.0
            cor = "#22c55e" if var_pct >= 0 else "#dc2626"
            fill_cor = "rgba(34, 197, 94, 0.16)" if var_pct >= 0 else "rgba(220, 38, 38, 0.18)"
            sinal = "+" if var_pct >= 0 else ""

            sub_px_html = ""
            if not serie_alt.empty and float(serie_alt.iloc[0]) > 0:
                pa_ini, pa_fim = float(serie_alt.iloc[0]), float(serie_alt.iloc[-1])
                var_alt_pct = ((pa_fim - pa_ini) / pa_ini) * 100.0
                diff_alt_abs = pa_fim - pa_ini
                cor_alt = "#22c55e" if var_alt_pct >= 0 else "#dc2626"
                sinal_alt = "+" if var_alt_pct >= 0 else ""
                sinal_abs_alt = "+" if diff_alt_abs >= 0 else "-"
                if ajustada:
                    sub_px_html = (
                        f"<div style='font-size:12px; opacity:0.90; margin-top:3px;'>"
                        f"Só valor da ação (sem div.): <strong style='color:{cor_alt};'>{sinal_alt}{fmt_num(var_alt_pct)}% ({sinal_abs_alt}{simb_moeda} {fmt_num(abs(diff_alt_abs))})</strong>"
                        f"</div>"
                    )
                else:
                    sub_px_html = (
                        f"<div style='font-size:12px; opacity:0.90; margin-top:3px;'>"
                        f"Com dividendos (ajustada): <strong style='color:{cor_alt};'>{sinal_alt}{fmt_num(var_alt_pct)}%</strong>"
                        f"</div>"
                    )

            with c_tb_px:
                st.markdown(
                    f"<div style='font-size:11px; opacity:0.65; letter-spacing:0.4px;'>BVMF • {ticker}</div>"
                    f"<div style='font-size:24px; font-weight:700; line-height:1.15; margin-top:1px;'>"
                    f"{simb_moeda} {fmt_num(p_fim)} "
                    f"<span style='font-size:14px; color:{cor}; font-weight:700;'>{sinal}{fmt_num(var_pct)}% ({lbl_per_exib})</span>"
                    f"</div>"
                    f"{sub_px_html}",
                    unsafe_allow_html=True,
                )

            fig = go.Figure()
            fmt_hover = "%{x|%d/%m/%Y %H:%M}" if (not usar_custom_range and periodo in ("1 D", "7 D")) else "%{x|%d/%m/%Y}"
            eh_candles = (not modo_comparar) and eh_candles_req and (not df_ohlcv.empty) and all(c in df_ohlcv.columns for c in ("Open", "High", "Low", "Close"))

            if modo_comparar:
                pct_base = ((serie / p_ini) - 1.0) * 100.0 if p_ini > 0 else serie * 0.0
                fig.add_trace(
                    go.Scatter(
                        x=pct_base.index, y=pct_base.values, mode="lines",
                        name=f"{ticker} ({sinal}{fmt_num(var_pct)}%)",
                        line=dict(color=cor, width=2.2),
                        hovertemplate=f"<b>{ticker}</b><br>{fmt_hover}: %{{y:+.2f}}%<extra></extra>",
                    )
                )
                y_all_vals = list(pct_base.values)
                if comp_ibov_on:
                    df_ib_c = buscar_ohlcv_preco("^BVSP".replace("^", ""), periodo, False) if False else None
                    try:
                        d_ib_g = buscar_dados_ibov_google({"30 D": "1 M", "6 M": "6 M", "YTD": "YTD", "1 A": "1 A", "5 A": "5 A", "10 A": "Máx", "15 A": "Máx"}.get(periodo, "1 A"))
                        s_ib = d_ib_g["serie"]
                        if not s_ib.empty:
                            s_ib = s_ib[s_ib.index >= serie.index[0]]
                            if not s_ib.empty and float(s_ib.iloc[0]) > 0:
                                pct_ib = ((s_ib / float(s_ib.iloc[0])) - 1.0) * 100.0
                                fig.add_trace(
                                    go.Scatter(
                                        x=pct_ib.index, y=pct_ib.values, mode="lines",
                                        name=f"IBOV ({pct_ib.iloc[-1]:+.2f}%)",
                                        line=dict(color="#60a5fa", width=1.8),
                                        hovertemplate=f"<b>IBOV</b><br>{fmt_hover}: %{{y:+.2f}}%<extra></extra>",
                                    )
                                )
                                y_all_vals.extend(list(pct_ib.values))
                    except Exception:
                        pass
                if comp_selic_on:
                    s_sel_c, _ = buscar_historico_selic_bcb()
                    if not s_sel_c.empty:
                        sub_sc = s_sel_c[(s_sel_c.index >= serie.index[0].normalize()) & (s_sel_c.index < serie.index[-1].normalize())]
                        if not sub_sc.empty:
                            fator_ac = ((1.0 + (sub_sc / 100.0)).cumprod() - 1.0) * 100.0
                            fig.add_trace(
                                go.Scatter(
                                    x=fator_ac.index, y=fator_ac.values, mode="lines",
                                    name=f"Tesouro Selic ({fator_ac.iloc[-1]:+.2f}%)",
                                    line=dict(color="#fbbf24", width=1.8, dash="dot"),
                                    hovertemplate=f"<b>Selic</b><br>{fmt_hover}: %{{y:+.2f}}%<extra></extra>",
                                )
                            )
                            y_all_vals.extend(list(fator_ac.values))
                cores_cmp = ["#a78bfa", "#38bdf8", "#f472b6", "#fb923c"]
                for idx_c, tk_c in enumerate(comp_tks[:4]):
                    s_cmp = buscar_serie_investidor10_chart(tk_c, periodo, ajustada) if not usar_custom_range else pd.Series(dtype=float)
                    if s_cmp.empty:
                        s_cmp = buscar_historico_preco(tk_c, periodo if not usar_custom_range else "15 A", ajustada)
                        if usar_custom_range and not s_cmp.empty:
                            s_cmp = s_cmp[(s_cmp.index.date >= dt_custom_ini) & (s_cmp.index.date <= dt_custom_fim)]
                    if not s_cmp.empty and float(s_cmp.iloc[0]) > 0:
                        pct_c = ((s_cmp / float(s_cmp.iloc[0])) - 1.0) * 100.0
                        fig.add_trace(
                            go.Scatter(
                                x=pct_c.index, y=pct_c.values, mode="lines",
                                name=f"{tk_c} ({pct_c.iloc[-1]:+.2f}%)",
                                line=dict(color=cores_cmp[idx_c % len(cores_cmp)], width=1.8),
                                hovertemplate=f"<b>{tk_c}</b><br>{fmt_hover}: %{{y:+.2f}}%<extra></extra>",
                            )
                        )
                        y_all_vals.extend(list(pct_c.values))
                y_min, y_max = min(y_all_vals), max(y_all_vals)
            elif eh_candles:
                x_ohlcv = list(range(len(df_ohlcv)))
                dt_fmt_c = "%d/%m/%Y %H:%M" if (not usar_custom_range and periodo in ("1 D", "7 D")) else "%d/%m/%Y"
                dt_lbls_c = [dt.strftime(dt_fmt_c) for dt in df_ohlcv.index]
                fig.add_trace(
                    go.Candlestick(
                        x=x_ohlcv,
                        open=df_ohlcv["Open"], high=df_ohlcv["High"],
                        low=df_ohlcv["Low"], close=df_ohlcv["Close"],
                        text=dt_lbls_c,
                        name=ticker,
                        increasing_line_color="#22c55e", decreasing_line_color="#dc2626",
                        increasing_fillcolor="#22c55e", decreasing_fillcolor="#dc2626",
                    )
                )
                if "Volume" in df_ohlcv.columns and df_ohlcv["Volume"].sum() > 0:
                    cores_vol = [
                        "rgba(34,197,94,0.35)" if float(c) >= float(o) else "rgba(220,38,38,0.35)"
                        for o, c in zip(df_ohlcv["Open"], df_ohlcv["Close"])
                    ]
                    fig.add_trace(
                        go.Bar(
                            x=x_ohlcv, y=df_ohlcv["Volume"], name="Volume",
                            marker_color=cores_vol, yaxis="y2",
                            customdata=[[lbl] for lbl in dt_lbls_c],
                            hovertemplate="%{customdata[0]}<br>Vol: %{y:,.0f}<extra></extra>",
                        )
                    )
                y_min = float(df_ohlcv["Low"].min())
                y_max = float(df_ohlcv["High"].max())
            else:
                x_idx = list(range(len(serie)))
                dt_fmt_s = "%d/%m/%Y %H:%M" if (not usar_custom_range and periodo in ("1 D", "7 D")) else "%d/%m/%Y"
                dt_lbls_s = [dt.strftime(dt_fmt_s) for dt in serie.index]
                ts_ms_s = [int(dt.timestamp() * 1000) for dt in serie.index]
                base_hover = p_ref_var if (not usar_custom_range and periodo == "1 D" and p_ref_var > 0) else p_ini
                pct_hover = [((float(v) / base_hover) - 1.0) * 100.0 if base_hover > 0 else 0.0 for v in serie.values]
                custom_s = [[lbl, pct, ts_m] for lbl, pct, ts_m in zip(dt_lbls_s, pct_hover, ts_ms_s)]
                fig.add_trace(
                    go.Scatter(
                        x=x_idx, y=serie.values, mode="lines", name=ticker,
                        customdata=custom_s,
                        line=dict(color=cor, width=2.1), fill="tozeroy", fillcolor=fill_cor,
                        hovertemplate=f"%{{customdata[0]}}<br><b>{simb_moeda} %{{y:,.2f}}</b> (%{{customdata[1]:+.2f}}%)<extra></extra>",
                    )
                )
                fig.add_trace(
                    go.Scatter(
                        x=[x_idx[-1]], y=[p_fim], mode="markers",
                        marker=dict(color=cor, size=7), hoverinfo="skip", showlegend=False,
                    )
                )
                y_min, y_max = float(serie.min()), float(serie.max())
                if not usar_custom_range and periodo == "1 D" and p_ref_var > 0 and abs(p_ref_var - p_fim) / max(0.01, p_fim) < 0.25:
                    fig.add_hline(
                        y=p_ref_var,
                        line_dash="dot",
                        line_width=1.1,
                        line_color="rgba(148,1
 4m58.3s

            if not modo_comparar and st.session_state[k_marcos]:
                pos_max = int(serie.values.argmax())
                pos_min = int(serie.values.argmin())
                v_max_m = float(serie.iloc[pos_max])
                v_min_m = float(serie.iloc[pos_min])
                fig.add_trace(
                    go.Scatter(
                        x=[pos_max, pos_min], y=[v_max_m, v_min_m],
                        mode="markers+text", text=[f"Máx {simb_moeda} {fmt_num(v_max_m)}", f"Mín {simb_moeda} {fmt_num(v_min_m)}"],
                        textposition=["top center", "bottom center"],
                        marker=dict(color=["#22c55e", "#f59e0b"], size=8, symbol="circle"),
                        textfont=dict(size=10.5), showlegend=False, hoverinfo="skip",
                    )
                )
                if st.session_state.get("usuario_email") and st.session_state.get("lancamentos"):
                    pos_m_usr = consolidar_carteira_por_ativo(st.session_state["lancamentos"])
                    if ticker in pos_m_usr and pos_m_usr[ticker]["pm"] > 0 and moeda_graf == "Real":
                        pm_u = float(pos_m_usr[ticker]["pm"])
                        fig.add_hline(y=pm_u, line_dash="dot", line_color="#60a5fa", line_width=1.4, annotation_text=f"Seu PM: R$ {fmt_num(pm_u)}", annotation_position="top left")

            if not modo_comparar and st.session_state[k_provs] and moeda_graf == "Real":
                divs_p = buscar_dividendos_ativo(ticker)
                if not divs_p.empty:
                    divs_win = divs_p[(divs_p.index >= serie.index[0]) & (divs_p.index <= serie.index[-1])]
                    if not divs_win.empty:
                        xs_d, ys_d, txts_d = [], [], []
                        for dt_d, vl_d in divs_win.items():
                            idx_near = int(serie.index.get_indexer([dt_d], method="nearest")[0])
                            xs_d.append(idx_near)
                            ys_d.append(float(serie.iloc[idx_near]))
                            txts_d.append(f"💰 Provento: R$ {fmt_num(float(vl_d))} ({dt_d.strftime('%d/%m/%Y')})")
                        fig.add_trace(
                            go.Scatter(
                                x=xs_d, y=ys_d, mode="markers", name="Proventos",
                                marker=dict(color="#fbbf24", size=9, symbol="diamond", line=dict(color="#ffffff", width=1)),
                                text=txts_d, hovertemplate="%{text}<extra></extra>", showlegend=False,
                            )
                        )

            margem_y = (y_max - y_min) * 0.06 if y_max > y_min else max(0.5, abs(y_max) * 0.05)
            if not modo_comparar and not eh_candles and y_min > 0:
                y_rng_lo = max(0.0, round(y_min * 0.98, 2))
                y_rng_hi = round(y_max * 1.02, 2)
            else:
                y_rng_lo = y_min - (margem_y * (2.4 if eh_candles else 0.7))
                if not modo_comparar:
                    y_rng_lo = max(0.0, y_rng_lo)
                y_rng_hi = y_max + (margem_y * 0.7)

            yaxis_cfg = dict(
                side="left",
                showgrid=True,
                gridcolor="rgba(255,255,255,0.14)",
                gridwidth=1,
                zeroline=modo_comparar,
                zerolinecolor="rgba(148,163,184,0.35)",
                tickprefix="" if modo_comparar else f"{simb_moeda} ",
                ticksuffix="%" if modo_comparar else "",
                tickformat=",.2f",
                tickfont=dict(size=11),
                range=[y_rng_lo, y_rng_hi],
                showspikes=True,
                spikemode="across",
                spikesnap="cursor",
                spikethickness=1,
                spikecolor="rgba(148,163,184,0.55)",
                spikedash="dash",
            )
            if not modo_comparar and not eh_candles:
                ticks_y = _calc_ticks_y_i10(y_rng_lo, y_rng_hi)
                yaxis_cfg["tickmode"] = "array"
                yaxis_cfg["tickvals"] = ticks_y
                yaxis_cfg["ticktext"] = [f"{simb_moeda} {fmt_num(tv)}" for tv in ticks_y]

            annots = []
            if not modo_comparar:
                annots.append(
                    dict(
                        xref="paper", x=1.006, y=p_fim, xanchor="left", yanchor="middle",
                        text=f"<b>{fmt_num(p_fim)}</b>", showarrow=False,
                        font=dict(color="white", size=11.5), bgcolor=cor, borderpad=4,
                    )
                )

            tickfmt_x = "%H:%M" if (not usar_custom_range and periodo == "1 D") else ("%d/%m %H:%M" if (not usar_custom_range and periodo == "7 D") else "%d/%m/%y")
            xaxis_cfg = dict(
                showgrid=False,
                zeroline=False,
                showline=True,
                linecolor="rgba(148,163,184,0.35)",
                linewidth=1,
                ticks="outside",
                ticklen=4,
                tickcolor="rgba(148,163,184,0.35)",
                tickfont=dict(size=11),
                tickformat=tickfmt_x,
                nticks=12,
                range=[serie.index[0], serie.index[-1]],
                rangeslider=dict(visible=False),
                showspikes=True,
                spikemode="across",
                spikesnap="cursor",
                spikethickness=1,
                spikecolor="rgba(148,163,184,0.55)",
                spikedash="dash",
            )
            if not modo_comparar:
                idx_ref_x = df_ohlcv.index if eh_candles else serie.index
                n_pts_x = len(idx_ref_x)
                xaxis_cfg["range"] = [-0.25, max(0.25, n_pts_x - 1 + 0.25)]
                xaxis_cfg.pop("tickformat", None)
                if not usar_custom_range and periodo == "1 D":
                    idxs_x = sorted({round(i * (n_pts_x - 1) / min(10, max(1, n_pts_x - 1))) for i in range(min(11, n_pts_x))})
                    if len(idxs_x) >= 3 and (idxs_x[-1] - idxs_x[-2]) < max(2, n_pts_x // 18):
                        idxs_x.pop(-2)
                    xaxis_cfg["tickmode"] = "array"
                    xaxis_cfg["tickvals"] = idxs_x
                    xaxis_cfg["ticktext"] = [idx_ref_x[i].strftime("%H:%M") for i in idxs_x]
                elif not usar_custom_range and periodo == "7 D":
                    dias_dist = sorted({dt.date() for dt in idx_ref_x})
                    if len(dias_dist) >= 2 and n_pts_x >= 12:
                        idxs_x = []
                        vistos_d = set()
                        for pos_i, dt_i in enumerate(idx_ref_x):
                            d_i = dt_i.date()
                            if d_i not in vistos_d:
                                vistos_d.add(d_i)
                                idxs_x.append(pos_i)
                        xaxis_cfg["tickmode"] = "array"
                        xaxis_cfg["tickvals"] = idxs_x
                        xaxis_cfg["ticktext"] = [idx_ref_x[i].strftime("%d/%m") for i in idxs_x]
                    else:
                        idxs_x = list(range(n_pts_x))
                        xaxis_cfg["tickmode"] = "array"
                        xaxis_cfg["tickvals"] = idxs_x
                        xaxis_cfg["ticktext"] = [idx_ref_x[i].strftime("%d/%m") for i in idxs_x]
                elif n_pts_x >= 2:
                    n_ticks_alvo = min(11, n_pts_x)
                    idxs_x = sorted({round(i * (n_pts_x - 1) / max(1, n_ticks_alvo - 1)) for i in range(n_ticks_alvo)})
                    if len(idxs_x) >= 3 and (idxs_x[-1] - idxs_x[-2]) < max(2, n_pts_x // 22):
                        idxs_x.pop(-2)
                    xaxis_cfg["tickmode"] = "array"
                    xaxis_cfg["tickvals"] = idxs_x
                    xaxis_cfg["ticktext"] = [idx_ref_x[i].strftime("%d/%m/%y") for i in idxs_x]

            layout_kw = dict(
                height=370 if eh_candles else 345,
                margin=dict(l=76, r=66, t=24 if modo_comparar else 14, b=42),
                paper_bgcolor="rgba(0,0,0,0)",
                plot_bgcolor="rgba(0,0,0,0)",
                separators=",.",
                showlegend=modo_comparar,
                legend=dict(orientation="h", yanchor="bottom", y=1.02, xanchor="left", x=0),
                hovermode="x unified",
                dragmode="pan",
                xaxis=xaxis_cfg,
                yaxis=yaxis_cfg,
                annotations=annots,
            )
            if eh_candles and "Volume" in df_ohlcv.columns and df_ohlcv["Volume"].sum() > 0:
                v_max = float(df_ohlcv["Volume"].max())
                layout_kw["yaxis2"] = dict(
                    overlaying="y", side="right", showgrid=False, showticklabels=False,
                    range=[0, v_max * 5.0 if v_max > 0 else 1],
                )
            fig.update_layout(**layout_kw)
            st.plotly_chart(
                fig,
                use_container_width=True,
                config={"scrollZoom": True, "displaylogo": False, "modeBarButtonsToRemove": ["zoom2d", "zoomIn2d", "zoomOut2d", "lasso2d", "select2d"]},
                key=f"{key_prefix}_plot_{ticker}",
            )
            fonte_graf_lbl = (
                "🟢 Fonte dos pontos: Investidor10"
                if usou_i10_graf
                else (
                    f"🟡 Fonte dos pontos: Yahoo Finance (Investidor10: {diag_i10_graf})"
                    if diag_i10_graf
                    else "🟡 Fonte dos pontos: Yahoo Finance"
                )
            )
            st.caption(f"💡 DEXTools: Segure **Shift + Botão Esquerdo e arraste** (ou clique em **📏 Medir**) para medir a variação (%) · Role o mouse para zoom · Arraste para mover. · {fonte_graf_lbl}")

        st.markdown("<div style='margin:10px 0 12px 0; border-top:1px solid rgba(128,128,128,0.22);'></div>", unsafe_allow_html=True)
        s1, s2 = st.columns([1.4, 1.2], vertical_alignment="bottom")
        with s1:
            valor_inv = st.number_input("Se você tivesse investido (R$):", min_value=10.0, value=1000.0, step=100.0, key=f"{key_prefix}_val_{ticker}")
        with s2:
            janela_sim = st.selectbox("Há:", ["1 mês", "6 meses", "1 ano", "5 anos", "10 anos", "15 anos"], index=2, key=f"{key_prefix}_jan_{ticker}")

        mapa_jan_per = {
            "1 mês": "30 D", "6 meses": "6 M", "1 ano": "1 A",
            "5 anos": "5 A", "10 anos": "10 A", "15 anos": "15 A",
        }
        per_sim_key = mapa_jan_per[janela_sim]
        reusa_adj = (not usar_custom_range) and (moeda_graf == "Real") and (per_sim_key == periodo)

        with ThreadPoolExecutor(max_workers=4) as ex_sim:
            f_selic = ex_sim.submit(buscar_historico_selic_bcb)
            f_divs = ex_sim.submit(buscar_dividendos_ativo, ticker)
            if reusa_adj and ajustada and not serie.empty:
                serie_sim = serie
                f_sim_adj_i10, f_sim_adj_yh = None, None
            elif reusa_adj and (not ajustada) and not serie_alt.empty:
                serie_sim = serie_alt
                f_sim_adj_i10, f_sim_adj_yh = None, None
            else:
                f_sim_adj_i10 = ex_sim.submit(buscar_serie_investidor10_chart, ticker, per_sim_key, True, cot_ref_live)
                f_sim_adj_yh = ex_sim.submit(buscar_historico_preco, ticker, per_sim_key, True, cot_ref_live)
                serie_sim = pd.Series(dtype=float)

            if reusa_adj and (not ajustada) and not serie.empty:
                serie_sim_simples = serie
                f_sim_smp_i10, f_sim_smp_yh = None, None
            elif reusa_adj and ajustada and not serie_alt.empty:
                serie_sim_simples = serie_alt
                f_sim_smp_i10, f_sim_smp_yh = None, None
            else:
                f_sim_smp_i10 = ex_sim.submit(buscar_serie_investidor10_chart, ticker, per_sim_key, False, cot_ref_live)
                f_sim_smp_yh = ex_sim.submit(buscar_historico_preco, ticker, per_sim_key, False, cot_ref_live)
                serie_sim_simples = pd.Series(dtype=float)

            serie_selic_bcb, _ = f_selic.result()
            divs_sim_s = f_divs.result()
            if serie_sim.empty:
                if f_sim_adj_i10 is not None:
                    serie_sim = f_sim_adj_i10.result()
                if serie_sim.empty and f_sim_adj_yh is not None:
                    serie_sim = f_sim_adj_yh.result()
            if serie_sim_simples.empty:
                if f_sim_smp_i10 is not None:
                    serie_sim_simples = f_sim_smp_i10.result()
                if serie_sim_simples.empty and f_sim_smp_yh is not None:
                    serie_sim_simples = f_sim_smp_yh.result()

        if serie_sim.empty:
            serie_max_fb = buscar_serie_max_ajustada(ticker)
            if not serie_max_fb.empty:
                deltas = {
                    "1 mês": pd.DateOffset(months=1), "6 meses": pd.DateOffset(months=6),
                    "1 ano": pd.DateOffset(years=1), "5 anos": pd.DateOffset(years=5),
                    "10 anos": pd.DateOffset(years=10), "15 anos": pd.DateOffset(years=15),
                }
                ref_fb = max(serie_max_fb.index.max().normalize(), pd.Timestamp(datetime.now(BRT).date()))
                serie_sim = serie_max_fb[serie_max_fb.index.normalize() >= (ref_fb - deltas[janela_sim])]

        if not serie_sim.empty:
            dt_base_ts = serie_sim.index[0].normalize()
            dt_fim_ts = serie_sim.index[-1].normalize()
            dias_corridos_sim = max(1, int((dt_fim_ts - dt_base_ts).days))
            data_efetiva = dt_base_ts.strftime("%d/%m/%Y")
            data_final_str = dt_fim_ts.strftime("%d/%m/%Y")

            p_base = float(serie_sim.iloc[0])
            p_hoje = float(serie_sim.iloc[-1])
            valor_acao_bruto = valor_inv * (p_hoje / p_base) if p_base > 0 else valor_inv
            ganho_acao = valor_acao_bruto - valor_inv
            if ganho_acao > 0.0 and valor_acao_bruto > 20_000.0:
                ir_acao = ganho_acao * 0.15
                valor_acao_liq = valor_acao_bruto - ir_acao
                nota_ir_acao = f"IR (15% s/ ganho): -R$ {fmt_num(ir_acao)} (venda &gt; R$ 20k/mês) · Reinvestindo dividendos"
            elif ganho_acao > 0.0:
                ir_acao = 0.0
                valor_acao_liq = valor_acao_bruto
                nota_ir_acao = "IR: Isento (venda ≤ R$ 20k/mês) · Reinvestindo dividendos"
            else:
                ir_acao = 0.0
                valor_acao_liq = valor_acao_bruto
                nota_ir_acao = "IR: Isento (sem lucro tributável) · Reinvestindo dividendos"

            ret_acao_pct = ((valor_acao_liq / valor_inv) - 1.0) * 100.0 if valor_inv > 0 else 0.0
            ret_acao_bruto_pct = ((valor_acao_bruto / valor_inv) - 1.0) * 100.0 if valor_inv > 0 else 0.0
            s_acao_liq = f"{'+' if ret_acao_pct >= 0 else ''}{fmt_num(ret_acao_pct, 2)}%"
            s_acao_bruto = f"{'+' if ret_acao_bruto_pct >= 0 else ''}{fmt_num(ret_acao_bruto_pct, 2)}%"
            cor_sim = "#22c55e" if valor_acao_liq >= valor_inv else "#ef4444"

            if not serie_sim_simples.empty:
                sub_ss = serie_sim_simples[serie_sim_simples.index.normalize() >= dt_base_ts]
                if not sub_ss.empty:
                    serie_sim_simples = sub_ss
            divs_win_sim = (
                divs_sim_s[(divs_sim_s.index.normalize() > dt_base_ts) & (divs_sim_s.index.normalize() <= dt_fim_ts)]
                if not divs_sim_s.empty else pd.Series(dtype=float)
            )

            bloco_sem_reinv_html = ""
            if not serie_sim_simples.empty and float(serie_sim_simples.iloc[0]) > 0:
                p_base_s = float(serie_sim_simples.iloc[0])
                p_hoje_s = float(serie_sim_simples.iloc[-1])
                qtd_acoes_sim = valor_inv / p_base_s
                valor_so_acao = qtd_acoes_sim * p_hoje_s
                ret_so_acao_pct = ((valor_so_acao / valor_inv) - 1.0) * 100.0 if valor_inv > 0 else 0.0
                divs_caixa_sim = qtd_acoes_sim * float(divs_win_sim.sum()) if not divs_win_sim.empty else 0.0
                valor_sem_reinv_bruto = valor_so_acao + divs_caixa_sim
                ganho_so_acao = valor_so_acao - valor_inv
                if ganho_so_acao > 0.0 and valor_so_acao > 20_000.0:
                    valor_sem_reinv_liq = valor_sem_reinv_bruto - (ganho_so_acao * 0.15)
                else:
                    valor_sem_reinv_liq = valor_sem_reinv_bruto
                ret_sem_reinv_pct = ((valor_sem_reinv_liq / valor_inv) - 1.0) * 100.0 if valor_inv > 0 else 0.0
                s_so_acao = f"{'+' if ret_so_acao_pct >= 0 else ''}{fmt_num(ret_so_acao_pct, 2)}%"
                s_sem_reinv = f"{'+' if ret_sem_reinv_pct >= 0 else ''}{fmt_num(ret_sem_reinv_pct, 2)}%"
                cor_sem_reinv = "#22c55e" if valor_sem_reinv_liq >= valor_inv else "#ef4444"
                bloco_sem_reinv_html = (
                    "<div style='font-size:12px; opacity:0.92; margin-top:4px; padding-top:4px; border-top:1px dashed rgba(128,128,128,0.28); line-height:1.4;'>"
                    f"Sem reinvestir div.: <strong style='color:{cor_sem_reinv};'>R$ {fmt_num(valor_sem_reinv_liq)} ({s_sem_reinv})</strong><br>"
                    f"<span style='font-size:11px; opacity:0.84;'>Só ação: <strong>R$ {fmt_num(valor_so_acao)}</strong> ({s_so_acao}) + Divs em caixa: <strong>R$ {fmt_num(divs_caixa_sim)}</strong></span>"
                    "</div>"
                )

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
                ret_selic_bruto_pct = ((valor_selic_bruto / valor_inv) - 1.0) * 100.0 if valor_inv > 0 else 0.0
                s_selic_liq = f"{'+' if ret_selic_pct >= 0 else ''}{fmt_num(ret_selic_pct, 2)}%"
                s_selic_bruto = f"{'+' if ret_selic_bruto_pct >= 0 else ''}{fmt_num(ret_selic_bruto_pct, 2)}%"

                partes_enc = []
                if iof_selic > 0.0:
                    partes_enc.append(f"IOF ({fmt_num(aliq_iof_selic, 0)}%): -R$ {fmt_num(iof_selic)}")
                partes_enc.append(f"IR ({fmt_num(aliq_ir_selic, 1)}%): -R$ {fmt_num(ir_selic)}")
                if custodia_b3 > 0.0:
                    partes_enc.append(f"Custódia B3: -R$ {fmt_num(custodia_b3)}")
                else:
                    partes_enc.append("Custódia B3: Isento (≤ R$ 10k)")
                txt_imp_selic = " · ".join(partes_enc)

                card_selic_html = (
                    "<div style='background:rgba(245,158,11,0.10); border:1px solid rgba(245,158,11,0.35); border-radius:8px; padding:12px 14px; "
                    "display:flex; flex-direction:column; justify-content:space-between; align-items:center; text-align:center; min-height:126px;'>"
                    "<div style='font-size:12px; font-weight:600; opacity:0.9; min-height:20px; display:flex; align-items:center; justify-content:center;'>"
                    f"🏛️ No Tesouro Selic ({data_efetiva} → {data_final_str})"
                    "</div>"
                    "<div style='min-height:34px; display:flex; align-items:baseline; justify-content:center; gap:8px; flex-wrap:wrap; margin:4px 0;'>"
                    f"<strong style='color:#fbbf24; font-size:21px;'>R$ {fmt_num(valor_selic_liq)}</strong>"
                    f"<span style='font-size:13px; font-weight:600; color:#fbbf24;'>({s_selic_liq} líq.)</span>"
                    "</div>"
                    "<div style='font-size:12px; font-weight:600; opacity:0.92; margin-bottom:3px;'>"
                    f"Calc. Cidadão (Bruto): R$ {fmt_num(valor_selic_bruto)} ({s_selic_bruto})"
                    "</div>"
                    f"<div style='font-size:11px; opacity:0.80; min-height:24px; display:flex; align-items:center; justify-content:center; line-height:1.35;'>{txt_imp_selic}</div>"
                    "</div>"
                )
                diff_sim = valor_acao_liq - valor_selic_liq
                diff_pp = ret_acao_pct - ret_selic_pct
                s_diff_pp = f"{'+' if diff_pp >= 0 else ''}{fmt_num(diff_pp, 2)} p.p."
                if diff_sim >= 0.0:
                    resumo_sim_html = (
                        f"<div style='margin-top:8px; padding:6px 10px; border-radius:6px; background:rgba(34,197,94,0.12); "
                        f"border-left:3px solid #22c55e; font-size:12.5px;'>"
                        f"🏆 <strong>{ticker}</strong> entregou <strong>R$ {fmt_num(diff_sim)}</strong> ({s_diff_pp}) a mais que o Tesouro Selic (Calculadora do Cidadão) "
                        f"(já descontando impostos e custódia nos dois casos)."
                        f"</div>"
                    )
                else:
                    resumo_sim_html = (
                        f"<div style='margin-top:8px; padding:6px 10px; border-radius:6px; background:rgba(245,158,11,0.12); "
                        f"border-left:3px solid #f59e0b; font-size:12.5px;'>"
                        f"🏛️ O <strong>Tesouro Selic (Calculadora do Cidadão)</strong> entregou <strong>R$ {fmt_num(abs(diff_sim))}</strong> ({fmt_num(abs(diff_pp), 2)} p.p.) a mais que {ticker} no período "
                        f"(já descontando impostos e custódia nos dois casos)."
                        f"</div>"
                    )
            else:
                card_selic_html = (
                    "<div style='background:rgba(128,128,128,0.10); border:1px solid rgba(128,128,128,0.28); border-radius:8px; padding:12px 14px; "
                    "display:flex; flex-direction:column; justify-content:space-between; align-items:center; text-align:center; min-height:126px;'>"
                    "<div style='font-size:12px; font-weight:600; opacity:0.9;'>🏛️ No Tesouro Selic</div>"
                    "<div style='font-size:13px; opacity:0.75;'>Indisponível no momento</div>"
                    "<div style='font-size:11px; opacity:0.7;'>API do Banco Central temporariamente indisponível.</div>"
                    "</div>"
                )
                resumo_sim_html = ""

            st.markdown(
                "<div style='display:grid; grid-template-columns:repeat(auto-fit,minmax(240px,1fr)); gap:12px; align-items:stretch; margin-top:6px;'>"
                "<div style='background:rgba(128,128,128,0.10); border:1px solid rgba(128,128,128,0.28); border-radius:8px; padding:12px 14px; "
                "display:flex; flex-direction:column; justify-content:space-between; align-items:center; text-align:center; min-height:126px;'>"
                "<div style='font-size:12px; font-weight:600; opacity:0.9; min-height:20px; display:flex; align-items:center; justify-content:center;'>"
                f"📈 Em {ticker} ({data_efetiva} → {data_final_str})"
                "</div>"
                "<div style='min-height:34px; display:flex; align-items:baseline; justify-content:center; gap:8px; flex-wrap:wrap; margin:4px 0;'>"
                f"<strong style='color:{cor_sim}; font-size:21px;'>R$ {fmt_num(valor_acao_liq)}</strong>"
                f"<span style='font-size:13px; font-weight:600; color:{cor_sim};'>({s_acao_liq} líq.)</span>"
                "</div>"
                "<div style='font-size:12px; font-weight:600; opacity:0.92; margin-bottom:3px;'>"
                f"Bruto (reinvestindo div.): R$ {fmt_num(valor_acao_bruto)} ({s_acao_bruto})"
                "</div>"
                f"{bloco_sem_reinv_html}"
                f"<div style='font-size:11px; opacity:0.80; min-height:24px; display:flex; align-items:center; justify-content:center; line-height:1.35; margin-top:4px;'>{nota_ir_acao}</div>"
                "</div>"
                f"{card_selic_html}"
                "</div>"
                f"{resumo_sim_html}",
                unsafe_allow_html=True,
            )

    with st.expander(f"📈 :blue-background[**{ticker}**] — Cotação & Simulador de Rentabilidade · clique para minimizar/maximizar", expanded=st.session_state.get(k_chart_open, expandir_padrao)):
        _frag_cotacao_sim()

    # --- BLOCO 2: HISTÓRICO FUNDAMENTALISTA ---
    with st.expander(f"📑 :blue-background[**{ticker}**] — Histórico Fundamentalista · clique para minimizar/maximizar", expanded=expandir_padrao):
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

    # --- BLOCO 3: SCORE, FAIXA DE PREÇO & DIAGNÓSTICO ---
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

        with st.expander(f"📊 :blue-background[**{ticker}**] — Score, Faixa de Preço & Diagnóstico · clique para minimizar/maximizar", expanded=expandir_padrao):
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
            st.markdown(
                "<div style='margin:10px 0 8px 0; border-top:1px solid rgba(128,128,128,0.22);'></div>",
                unsafe_allow_html=True,
            )
            st.markdown(partes_just_rx[0])
            if len(partes_just_rx) > 1 and partes_just_rx[1].strip():
                st.markdown(
                    "<div style='margin:10px 0 8px 0; border-top:1px solid rgba(128,128,128,0.20);'></div>",
                    unsafe_allow_html=True,
                )
                st.markdown(partes_just_rx[1], unsafe_allow_html=True)

    # --- BLOCO 4 E 5: SIMULADOR DE RENDA PASSIVA, SAZONALIDADE DE DIVIDENDOS & CHECKLIST BUY & HOLD ---
    if base_ativo:
        _, selic_aa_atual = buscar_historico_selic_bcb()
        cot_sim = float(base_ativo.get("cotacao") or 0.0)
        if cot_sim <= 0.0 and not serie.empty:
            cot_sim = float(serie.iloc[-1])
        if cot_sim <= 0.0:
            s_fb_c = buscar_historico_preco(ticker, "30 D", True)
            if not s_fb_c.empty:
                cot_sim = float(s_fb_c.iloc[-1])

        with st.expander(f"💰 :blue-background[**{ticker}**] — Simulador de Renda Passiva · clique para minimizar/maximizar", expanded=expandir_padrao):
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
                selic_badge_txt = f"Taxa DI / Selic Efetiva (BCB): {fmt_num(selic_aa_atual, 2)}% a.a." if selic_aa_atual else "Taxa DI / Selic: indisponível"
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
                cap_cdb_225 = _calc_cdb_di_capital_mensal(meta_mensal, selic_aa_atual, 0.225)
                cap_cdb_15 = _calc_cdb_di_capital_mensal(meta_mensal, selic_aa_atual, 0.15)
                total_mes_225 = cap_cdb_225 + meta_mensal
                card_selic_rp = (
                    "<div style='background:rgba(245,158,11,0.10); border:1px solid rgba(245,158,11,0.35); border-radius:8px; padding:12px 14px; "
                    "display:flex; flex-direction:column; justify-content:space-between; align-items:center; text-align:center; min-height:112px;'>"
                    "<div style='font-size:12px; opacity:0.88; min-height:22px; display:flex; align-items:center; justify-content:center;'>"
                    "🏦 Capital em CDB 100% DI Hoje"
                    "</div>"
                    "<div style='min-height:36px; display:flex; align-items:center; justify-content:center; margin:4px 0;'>"
                    f"<span style='font-size:21px; font-weight:700; color:#fbbf24;'>R$ {fmt_num(cap_cdb_225)}</span>"
                    "</div>"
                    "<div style='font-size:11px; opacity:0.82; min-height:32px; display:flex; align-items:center; justify-content:center; line-height:1.35;'>"
                    f"Total líq. no mês: R$ {fmt_num(total_mes_225)} (22,5% IR · 30/365d) · c/ 15% IR (&gt;2a): R$ {fmt_num(cap_cdb_15)}"
                    "</div>"
                    "</div>"
                )
            else:
                cap_cdb_225 = None
                card_selic_rp = (
                    "<div style='background:rgba(128,128,128,0.10); border:1px solid rgba(128,128,128,0.28); border-radius:8px; padding:12px 14px; "
                    "display:flex; flex-direction:column; justify-content:space-between; align-items:center; text-align:center; min-height:112px;'>"
                    "<div style='font-size:12px; opacity:0.88; min-height:22px; display:flex; align-items:center; justify-content:center;'>🏦 Capital em CDB 100% DI Hoje</div>"
                    "<div style='font-size:14px; opacity:0.75; min-height:36px; display:flex; align-items:center; justify-content:center;'>Indisponível</div>"
                    "<div style='font-size:11px; opacity:0.7; min-height:32px; display:flex; align-items:center; justify-content:center;'>Taxa DI/Selic do BCB indisponível.</div>"
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

                if cap_cdb_225 and cap_cdb_225 > 0:
                    diff_cap_rp = custo_total_nec - cap_cdb_225
                    if diff_cap_rp <= 0:
                        st.markdown(
                            f"<div style='margin-top:8px; padding:6px 10px; border-radius:6px; background:rgba(34,197,94,0.12); "
                            f"border-left:3px solid #22c55e; font-size:12.5px;'>"
                            f"💡 Pelo yield atual de <strong>{ticker}</strong>, você precisa de <strong>R$ {fmt_num(abs(diff_cap_rp))}</strong> a menos que em um CDB 100% DI (1 mês, IR de 22,5%, base 30/365d) para receber R$ {fmt_num(meta_mensal)}/mês líquidos."
                            f"</div>",
                            unsafe_allow_html=True,
                        )
                    else:
                        st.markdown(
                            f"<div style='margin-top:8px; padding:6px 10px; border-radius:6px; background:rgba(245,158,11,0.12); "
                            f"border-left:3px solid #f59e0b; font-size:12.5px;'>"
                            f"💡 Hoje, um <strong>CDB 100% DI</strong> exige <strong>R$ {fmt_num(diff_cap_rp)}</strong> a menos de capital inicial que <strong>{ticker}</strong> (1 mês, já descontando 22,5% de IR, base 30/365d); porém ações tendem a reajustar proventos pela inflação no longo prazo."
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

        with st.expander(f"📅 :blue-background[**{ticker}**] — Sazonalidade de Proventos & 🛡️ Checklist Buy & Hold · clique para minimizar/maximizar", expanded=expandir_padrao):
            col_saz, col_bh = st.columns([1.05, 1.15], gap="large")
            with col_saz:
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


def mapear_trilha(setor: str, subsetor: str = "", segmento: str = "") -> str:
    s = _norm_txt(f"{setor} {subsetor} {segmento}")
    if any(b in s for b in ("banco", "intermediarios financeiros", "previdencia", "seguro", "servicos financeiros")):
        return "FINANCEIRO"
    if any(u in s for u in ("utilidade publica", "energia", "eletric", "saneamento", "agua", "transmiss", "transporte", "rodovia", "porto", "ferrovia", "concess")) or (re.search(r"\bgas\b", s) and "petroleo" not in s):
        return "CONCESSOES_UTILITIES"
    if any(c in s for c in ("petroleo", "biocombustiveis", "mineracao", "siderurgia", "metalurgia", "madeira e papel", "papel e celulose", "celulose", "agropecuaria", "commodit")):
        return "COMMODITIES_CICLICAS"
    if any(r in s for r in ("construcao civil", "incorporac", "exploracao de imoveis", "imobiliari")):
        return "REAL_ESTATE"
    return "GERAL_VAREJO_TECH_IND"


def calcular_score(d: dict, pt_med: float | None, pt_proj: float | None, pt_bazin: float | None, graham: float | None) -> dict:
    cot = float(d.get("cotacao") or 0.0)
    setor_str = str(d.get("setor_oficial") or d.get("setor_nome") or d.get("setor") or "")
    trilha = d.get("trilha") or mapear_trilha(setor_str, str(d.get("subsetor") or ""), str(d.get("segmento") or ""))
    eh_banco_seg = (trilha == "FINANCEIRO") or bool(d.get("eh_banco_seg", False))
    eh_utilities = (trilha == "CONCESSOES_UTILITIES")
    eh_ciclica = (trilha == "COMMODITIES_CICLICAS")
    eh_real_estate = (trilha == "REAL_ESTATE")
    eh_transmissora = bool(d.get("eh_transmissora", False))

    pl = d.get("pl")
    pvp = d.get("pvp")
    lpa = d.get("lpa")
    vpa = d.get("vpa")
    roe = d.get("roe")
    roic = d.get("roic")
    marg_liq = d.get("marg_liq")
    marg_ebit = d.get("marg_ebit")
    marg_bruta = d.get("marg_bruta")
    ev_ebitda = d.get("ev_ebitda")
    liq_corr = d.get("liq_corr")
    div_brut_patrim = d.get("div_brut_patrim")
    div_liq_ebitda = d.get("div_liq_ebitda")
    div_liq_fco = d.get("div_liq_fco")
    cresc_rec_5a = d.get("cresc_rec_5a")
    cresc_lucro_5a = d.get("cresc_lucro_5a")
    fcf_yield = d.get("fcf_yield")

    dy_12m = float(d.get("dy_12m") or 0.0)
    dpa_12m_v = float(d.get("dpa_12m") or 0.0)
    dpa_med_5a = float(d.get("dpa_med_6a") or 0.0)
    dpa_base = float(d.get("dpa_base") or (min(dpa_12m_v, dpa_med_5a * 1.25) if (dpa_12m_v > 0 and dpa_med_5a > 0) else dpa_12m_v))
    anos_hist = int(d.get("anos_hist") or 0)
    anos_divs_consec = int(d.get("anos_divs_consec") or anos_hist or 0)
    pt_mult_justo = d.get("pt_mult_justo")

    ifr_14 = d.get("ifr_14")
    mm20 = d.get("mm20")
    mm50 = d.get("mm50")
    mm200 = d.get("mm200")
    mm20_incl_pos = d.get("mm20_incl_pos")
    dist_mm20_pct = d.get("dist_mm20_pct")
    dist_mm200_pct = d.get("dist_mm200_pct")
    dist_max_52s_pct = d.get("dist_max_52s_pct")
    razao_volume = d.get("razao_volume")
    ret_5d_pct = d.get("ret_5d_pct")
    var_dia_pct = d.get("var_dia_pct")
    forca_rel_ibov = d.get("forca_rel_ibov_30d")

    news_score = float(d.get("news_score") or 0.0)
    news_resumo = str(d.get("news_resumo") or "⚪ Neutro")
    news_tem_rj = bool(d.get("news_tem_rj", False)) or ("/ RJ" in news_resumo)

    # Transmissoras elétricas: prioriza FCO/EBITDA regulatório para endividamento
    div_liq_efetiva = div_liq_ebitda
    if eh_transmissora and div_liq_fco is not None and div_liq_fco >= 0:
        div_liq_efetiva = min(div_liq_ebitda, div_liq_fco) if div_liq_ebitda is not None else div_liq_fco

    # === 1) VALUATION ROBUSTO: TRIPÉ DE MÉTODOS INDEPENDENTES + MS ===
    pts_tripe = [float(x) for x in (pt_bazin, graham, pt_mult_justo) if x is not None and float(x) > 0]
    n_metodos = len(pts_tripe)
    fator_confianca = 0.65 if n_metodos == 1 else (0.85 if n_metodos == 2 else 1.0)

    if pts_tripe and cot > 0:
        pts_ord = sorted(pts_tripe)
        mid_m = len(pts_ord) // 2
        pt_justo_consolidado = pts_ord[mid_m] if (len(pts_ord) % 2 == 1) else ((pts_ord[mid_m - 1] + pts_ord[mid_m]) / 2.0)
        ms_bruta = ((pt_justo_consolidado - cot) / pt_justo_consolidado) * 100.0 if pt_justo_consolidado > 0 else -100.0
        ms_consolidada = max(-100.0, min(150.0, ms_bruta))
        ms_para_pts = max(-40.0, min(60.0, ms_consolidada))
        pts_ms = max(0.0, min(20.0, ((ms_para_pts + 40.0) / 100.0) * 20.0)) * fator_confianca
    else:
        pt_justo_consolidado = None
        ms_consolidada = None
        pts_ms = 0.0

    # === 2) FAIXA DE PREÇO DO MODELO (CONSISTENTE E UNIVERSAL) ===
    cands_teto = []
    if graham and graham > 0:
        cands_teto.append(float(graham))
    em_capex_utilities = eh_utilities and dy_12m < 4.5 and (div_liq_efetiva is None or div_liq_efetiva < 3.0) and pt_mult_justo and float(pt_mult_justo) > 0
    if em_capex_utilities:
        cands_teto.append(float(pt_mult_justo) * 0.85)
    elif pt_bazin and pt_bazin > 0:
        cands_teto.append(float(pt_bazin) * 0.85)
    preco_teto_modelo = min(cands_teto) if cands_teto else None

    if eh_banco_seg:
        fator_roe_sp = max(0.80, min(1.60, float(roe) / 14.0)) if roe is not None else 1.0
        preco_sobrepreco = (float(vpa) * fator_roe_sp * 1.15) if (vpa is not None and float(vpa) > 0) else (float(graham) * 1.15 if graham else None)
    else:
        dpa_ref_sp = max(dpa_12m_v, dpa_med_5a * 0.85) if (dpa_12m_v > 0 or dpa_med_5a > 0) else 0.0
        p_yield_4pct = (dpa_ref_sp / 0.04) if dpa_ref_sp > 0 else None
        p_graham_125 = (float(graham) * 1.25) if (graham and graham > 0) else None
        if em_capex_utilities and pt_mult_justo:
            cands_sp = [x for x in (p_graham_125, float(pt_mult_justo) * 1.15) if x is not None]
        else:
            cands_sp = [x for x in (p_graham_125, p_yield_4pct) if x is not None]
        preco_sobrepreco = min(cands_sp) if cands_sp else None

    if preco_sobrepreco is not None and preco_teto_modelo is not None and preco_teto_modelo > 0:
        preco_sobrepreco = max(preco_teto_modelo * 1.15, preco_sobrepreco)

    # === 3) SCORE LONGO PRAZO (0 a 100): Val(35) + Rent(30) + Saúde(30) + News(5) ===
    if eh_banco_seg:
        pts_pvp_m = (max(0.0, min(4.0, ((2.2 - pvp) / 1.4) * 4.0)) + (1.0 if pvp <= 1.0 else 0.0)) if (pvp and pvp > 0) else 0.0
        pts_pl_m = max(0.0, min(5.0, ((16.0 - pl) / 12.0) * 5.0)) if (pl and pl > 0) else 0.0
        pts_mult = min(10.0, pts_pvp_m + pts_pl_m)
    elif eh_ciclica:
        pts_ev = max(0.0, min(5.0, ((8.0 - ev_ebitda) / 4.5) * 5.0)) if (ev_ebitda and ev_ebitda > 0) else 0.0
        pts_pl_m = max(0.0, min(3.0, ((15.0 - pl) / 11.0) * 3.0)) if (pl and pl > 0) else 0.0
        pts_pvp_m = max(0.0, min(2.0, ((2.2 - pvp) / 1.4) * 2.0)) if (pvp and pvp > 0) else 0.0
        pts_mult = min(10.0, pts_ev + pts_pl_m + pts_pvp_m)
    else:
        pts_pvp_m = (max(0.0, min(3.0, ((2.5 - pvp) / 1.5) * 3.0)) + (1.0 if pvp < 1.0 else 0.0)) if (pvp and pvp > 0) else 0.0
        pts_pl_m = max(0.0, min(4.0, ((20.0 - pl) / 15.0) * 4.0)) if (pl and pl > 0) else 0.0
        ev_lim = 11.0 if eh_utilities else 12.0
        pts_ev = max(0.0, min(2.0, ((ev_lim - ev_ebitda) / 6.0) * 2.0)) if (ev_ebitda and ev_ebitda > 0) else 0.0
        pts_mult = min(10.0, pts_pvp_m + pts_pl_m + pts_ev)

    if eh_ciclica and fcf_yield is not None:
        pts_div = min(5.0, min(3.0, (max(0.0, dy_12m) / 8.0) * 3.0) + max(0.0, min(2.0, (fcf_yield / 10.0) * 2.0)))
    elif trilha == "GERAL_VAREJO_TECH_IND" and dy_12m < 3.0 and roe is not None and roe >= 16.0:
        pts_div = min(5.0, (max(0.0, dy_12m) / 6.0) * 2.5 + (min(anos_hist, 5) / 5.0) * 1.5 + 1.5)
    elif dy_12m <= 0.0 and dpa_med_5a <= 0.0 and anos_hist <= 0:
        pts_div = 0.0
    else:
        pts_div = min(5.0, min(3.5, (max(0.0, dy_12m) / 8.0) * 3.5) + (min(1.5, (min(anos_hist, 5) / 5.0) * 1.5) if anos_hist > 0 else 0.0))
    pts_val_lp = min(35.0, pts_ms + pts_mult + pts_div)

    # 3.2 Rentabilidade (30 pts) pelas 5 Trilhas
    if eh_banco_seg:
        pts_roe_lp = 0.0 if (roe is None or roe <= 0) else ((roe / 14.0) * 13.0 if roe <= 14.0 else min(20.0, 13.0 + ((roe - 14.0) / 8.0) * 7.0))
        cresc_lpa_ref = cresc_lucro_5a if cresc_lucro_5a is not None else cresc_rec_5a
        if cresc_lpa_ref is not None:
            pts_estab = max(1.0 if (pl and pl > 0) else 0.0, min(10.0, ((cresc_lpa_ref + 10.0) / 25.0) * 10.0))
        elif marg_liq is not None and marg_liq > 0.0:
            pts_estab = min(10.0, (marg_liq / 20.0) * 10.0)
        else:
            pts_estab = 6.5 if (pl and pl > 0 and roe and roe >= 10.0) else (3.5 if (pl and pl > 0) else 0.0)
        pts_rent_lp = min(30.0, pts_roe_lp + pts_estab)
    elif eh_utilities:
        pts_roic_lp = min(12.0, (roic / 15.0) * 12.0) if (roic and roic > 0) else (min(12.0, (roe / 18.0) * 12.0) if (roe and roe > 0) else 0.0)
        pts_roe_lp = min(10.0, (roe / 18.0) * 10.0) if (roe and roe > 0) else 0.0
        pts_me_lp = min(8.0, (marg_ebit / 30.0) * 8.0) if (marg_ebit and marg_ebit > 0) else (min(8.0, (marg_liq / 20.0) * 8.0) if (marg_liq and marg_liq > 0) else 0.0)
        pts_rent_lp = min(30.0, pts_roic_lp + pts_roe_lp + pts_me_lp)
    elif eh_ciclica:
        pts_roic_lp = min(16.0, (roic / 20.0) * 16.0) if (roic and roic > 0) else (min(16.0, (roe / 22.0) * 16.0) if (roe and roe > 0) else 0.0)
        pts_meb_lp = min(8.0, (marg_ebit / 25.0) * 8.0) if (marg_ebit and marg_ebit > 0) else (min(8.0, (marg_liq / 18.0) * 8.0) if (marg_liq and marg_liq > 0) else 0.0)
        pts_roe_lp = min(6.0, (roe / 22.0) * 6.0) if (roe and roe > 0) else 0.0
        pts_rent_lp = min(30.0, pts_roic_lp + pts_meb_lp + pts_roe_lp)
    elif eh_real_estate:
        pts_roe_lp = min(15.0, (roe / 20.0) * 15.0) if (roe and roe > 0) else 0.0
        mb_ref = marg_bruta if marg_bruta is not None else (marg_ebit if marg_ebit is not None else marg_liq)
        pts_mb_lp = min(15.0, (mb_ref / 35.0) * 15.0) if (mb_ref and mb_ref > 0) else 0.0
        pts_rent_lp = min(30.0, pts_roe_lp + pts_mb_lp)
    else:
        pts_roe_lp = min(12.0, (roe / 24.0) * 12.0) if (roe and roe > 0) else 0.0
        pts_roic_lp = min(10.0, (roic / 20.0) * 10.0) if (roic and roic > 0) else (min(10.0, (roe / 24.0) * 10.0) if (roe and roe > 0) else 0.0)
        pts_ml_lp = min(8.0, (marg_liq / 18.0) * 8.0) if (marg_liq and marg_liq > 0) else 0.0
        pts_rent_lp = min(30.0, pts_roe_lp + pts_roic_lp + pts_ml_lp)

    # 3.3 Saúde & Solvência (30 pts) pelas 5 Trilhas
    if eh_banco_seg:
        pts_prov = min(10.0, (min(anos_divs_consec, 6) / 6.0) * 10.0) if anos_divs_consec > 0 else 0.0
        cresc_b = cresc_rec_5a if cresc_rec_5a is not None else cresc_lucro_5a
        pts_cresc = max(0.0, min(10.0, ((cresc_b + 5.0) / 20.0) * 10.0)) if cresc_b is not None else 4.5
        if roe is not None and roe > 0 and (pl is None or pl > 0):
            pvp_justo_b = max(0.60, min(2.00, (roe - 5.0) / 9.0))
            if pvp is not None and pvp > 0:
                pts_solv = 10.0 if (roe >= 12.0 and pvp <= pvp_justo_b * 1.15) else (7.5 if pvp <= pvp_justo_b * 1.40 else 5.0)
            else:
                pts_solv = 7.5 if roe >= 12.0 else 5.5
        else:
            pts_solv = 0.0
        pts_saude_lp = min(30.0, pts_prov + pts_cresc + pts_solv)
    elif eh_utilities:
        if div_liq_efetiva is not None:
            pts_divida = 14.0 if div_liq_efetiva <= 2.5 else (14.0 - ((div_liq_efetiva - 2.5) / 1.0) * 5.0 if div_liq_efetiva <= 3.5 else (max(0.0, 9.0 - ((div_liq_efetiva - 3.5) / 1.0) * 9.0)))
        elif div_brut_patrim is not None:
            pts_divida = 14.0 if div_brut_patrim <= 1.5 else (9.0 if div_brut_patrim <= 3.0 else max(0.0, 9.0 - (div_brut_patrim - 3.0) * 4.0))
        else:
            pts_divida = 7.0
        pts_liq = (4.0 if liq_corr >= 1.1 else max(0.0, ((liq_corr - 0.7) / 0.4) * 4.0)) if liq_corr is not None else 2.0
        pts_marg_estab = 0.0
        if marg_ebit is not None and marg_ebit >= 20.0:
            pts_marg_estab += 7.0
        elif marg_ebit is not None and marg_ebit > 0.0:
            pts_marg_estab += (marg_ebit / 20.0) * 7.0
        elif roic is not None and roic >= 9.0:
            pts_marg_estab += 6.0
        pts_cresc_u = max(0.0, min(5.0, ((cresc_rec_5a + 5.0) / 20.0) * 5.0)) if cresc_rec_5a is not None else 2.5
        pts_saude_lp = min(30.0, pts_divida + pts_liq + pts_marg_estab + pts_cresc_u)
    elif eh_ciclica:
        if div_liq_efetiva is not None:
            pts_divida = 16.0 if div_liq_efetiva < 1.5 else (16.0 - ((div_liq_efetiva - 1.5) / 1.0) * 6.0 if div_liq_efetiva <= 2.5 else max(0.0, 10.0 - ((div_liq_efetiva - 2.5) / 1.5) * 10.0))
        elif div_brut_patrim is not None:
            pts_divida = 16.0 if div_brut_patrim <= 0.8 else max(0.0, 16.0 - ((div_brut_patrim - 0.8) / 2.2) * 16.0)
        else:
            pts_divida = 8.0
        if fcf_yield is not None:
            pts_fcf_c = 10.0 if fcf_yield >= 8.0 else max(0.0, min(10.0, 3.0 + (fcf_yield / 8.0) * 7.0))
        elif roic is not None and roic > 0:
            pts_fcf_c = min(10.0, (roic / 15.0) * 8.0 + (2.0 if dy_12m >= 5.0 else 0.0))
        else:
            pts_fcf_c = 4.0
        pts_liq = (4.0 if liq_corr >= 0.85 else max(0.0, ((liq_corr - 0.50) / 0.35) * 4.0)) if liq_corr is not None else 2.0
        pts_saude_lp = min(30.0, pts_divida + pts_fcf_c + pts_liq)
    elif eh_real_estate:
        if div_brut_patrim is not None:
            pts_div_re = 15.0 if div_brut_patrim <= 0.5 else (15.0 - ((div_brut_patrim - 0.5) / 1.0) * 7.0 if div_brut_patrim <= 1.5 else max(0.0, 8.0 - (div_brut_patrim - 1.5) * 8.0))
        else:
            pts_div_re = 7.5
        pts_liq_re = (8.0 if liq_corr >= 1.5 else max(0.0, ((liq_corr - 0.8) / 0.7) * 8.0)) if liq_corr is not None else 4.0
        pts_giro_re = max(0.0, min(7.0, ((cresc_rec_5a + 5.0) / 20.0) * 7.0)) if cresc_rec_5a is not None else 3.5
        pts_saude_lp = min(30.0, pts_div_re + pts_liq_re + pts_giro_re)
    else:
        if div_liq_efetiva is not None:
            pts_divida = 12.0 if div_liq_efetiva <= 1.5 else (12.0 - ((div_liq_efetiva - 1.5) / 1.5) * 7.0 if div_liq_efetiva <= 3.0 else max(0.0, 5.0 - ((div_liq_efetiva - 3.0) / 1.5) * 5.0))
        elif div_brut_patrim is not None:
            pts_divida = 12.0 if div_brut_patrim <= 0.5 else max(0.0, 12.0 - ((div_brut_patrim - 0.5) / 2.5) * 12.0)
        else:
            pts_divida = 6.0
        pts_liq = (8.0 if liq_corr >= 1.4 else max(0.0, ((liq_corr - 0.8) / 0.6) * 8.0)) if liq_corr is not None else 4.0
        pts_cresc = max(0.0, min(10.0, ((cresc_rec_5a + 5.0) / 23.0) * 10.0)) if cresc_rec_5a is not None else 4.0
        pts_saude_lp = min(30.0, pts_divida + pts_liq + pts_cresc)

    pts_news_lp = max(0.0, min(5.0, ((news_score + 10.0) / 20.0) * 5.0))
    score_lp_bruto = pts_val_lp + pts_rent_lp + pts_saude_lp + pts_news_lp

    # === 4) TRAVA ANTI-ARMADILHA (VALUE TRAP) ===
    armadilha_motivos = []
    if (not eh_banco_seg) and ((marg_liq is not None and marg_liq < 0) or (lpa is not None and lpa <= 0)):
        armadilha_motivos.append("prejuízo operacional (Margem Líq. / LPA ≤ 0)")
    if vpa is not None and float(vpa) <= 0:
        armadilha_motivos.append("patrimônio líquido negativo (VPA ≤ 0)")
    if roe is not None and roe <= 0:
        armadilha_motivos.append(f"destruição de capital (ROE {fmt_num(roe, 1)}%)")
    if div_liq_efetiva is not None and div_liq_efetiva > 4.5 and trilha in ("CONCESSOES_UTILITIES", "GERAL_VAREJO_TECH_IND"):
        if not (eh_transmissora and div_liq_fco is not None and div_liq_fco <= 4.5):
            armadilha_motivos.append(f"alavancagem perigosa (Dív.Líq/EBITDA {fmt_num(div_liq_efetiva)}x > 4,5x)")
    if news_tem_rj:
        armadilha_motivos.append("risco de falência / recuperação judicial")

    eh_value_trap = len(armadilha_motivos) > 0
    score_lp = round(min(score_lp_bruto, 50.0) if eh_value_trap else min(100.0, score_lp_bruto), 1)

    # === 5) SCORE CURTO PRAZO (0 a 100): Médias(35) + IFR(30) + Vol(15) + IBOV(10) + News(10) ===
    if mm20 is None and mm50 is None and mm200 is None:
        pts_medias = 17.5
    else:
        pts_mm200 = 7.0
        if dist_mm200_pct is not None:
            pts_mm200 = 15.0 if dist_mm200_pct >= 0.0 else (7.0 if dist_mm200_pct >= -5.0 else (3.0 if dist_mm200_pct >= -10.0 else 0.0))
        pts_mm50_al = 6.0
        if mm50 is not None and cot > 0:
            pts_mm50_al = 12.0 if (cot >= mm50 and (mm20 is None or mm20 >= mm50)) else (6.0 if (cot >= mm50 or (mm20 is not None and mm20 >= mm50)) else 0.0)
        pts_mm20_tac = 4.0
        if dist_mm20_pct is not None:
            if -2.0 <= dist_mm20_pct <= 5.0 and (mm20_incl_pos is True or mm20_incl_pos is None):
                pts_mm20_tac = 8.0
            elif -4.0 <= dist_mm20_pct <= 8.0:
                pts_mm20_tac = 4.0
            else:
                pts_mm20_tac = 0.0
        pts_medias = min(35.0, pts_mm200 + pts_mm50_al + pts_mm20_tac)

    trava_ifr_mm200 = False
    if ifr_14 is not None:
        if 38.0 <= ifr_14 <= 50.0:
            pts_ifr = 30.0 - (abs(ifr_14 - 44.0) / 6.0) * 1.5
        elif 30.0 <= ifr_14 < 38.0:
            pts_ifr = 23.0 + ((ifr_14 - 30.0) / 8.0) * 5.5
        elif ifr_14 < 30.0:
            pts_ifr = max(14.0, 22.0 - (30.0 - ifr_14) * 0.7)
        elif ifr_14 < 70.0:
            pts_ifr = max(7.0, 28.5 - ((ifr_14 - 50.0) / 20.0) * 21.5)
        else:
            pts_ifr = max(0.0, 5.0 - ((ifr_14 - 70.0) / 15.0) * 5.0)
        if mm200 is not None and cot > 0 and cot < (mm200 * 0.90):
            trava_ifr_mm200 = True
            pts_ifr = min(pts_ifr, 12.0)
    else:
        pts_ifr = 15.0

    trava_vol_dist = False
    if razao_volume is not None:
        em_distribuicao = (
            (razao_volume >= 1.2 and ret_5d_pct is not None and ret_5d_pct < -2.0)
            or (var_dia_pct is not None and var_dia_pct < -2.0 and mm20 is not None and cot > 0 and cot < mm20)
            or (mm20 is not None and cot > 0 and cot < mm20 * 0.97 and news_score < 0)
        )
        if em_distribuicao:
            trava_vol_dist = True
            pts_vol = 3.0
        elif razao_volume >= 1.2 and (ret_5d_pct is None or ret_5d_pct >= 0.0):
            pts_vol = 15.0
        elif razao_volume >= 1.2:
            pts_vol = 9.0
        else:
            pts_vol = max(3.0, min(11.0, (razao_volume / 1.2) * 11.0))
    else:
        pts_vol = 7.5

    if forca_rel_ibov is not None:
        if forca_rel_ibov > 5.0:
            pts_ibov = 10.0
        elif forca_rel_ibov < -5.0:
            pts_ibov = 0.0
        else:
            pts_ibov = 5.0 + (forca_rel_ibov / 5.0) * 5.0
    else:
        pts_ibov = 5.0

    pts_news_cp = max(0.0, min(10.0, ((news_score + 10.0) / 20.0) * 10.0))

    score_cp = round(min(100.0, pts_medias + pts_ifr + pts_vol + pts_ibov + pts_news_cp), 1)
    score_geral_bruto = (0.70 * score_lp) + (0.30 * score_cp)
    score_geral = round(min(score_geral_bruto, score_lp + 8.0) if score_lp < 55.0 else min(100.0, score_geral_bruto), 1)

    # === 6) ÁRVORE DE DECISÃO DOS VEREDITOS (SEQUÊNCIA EXATA) ===
    if (marg_liq is not None and marg_liq < 0) and trilha != "FINANCEIRO":
        veredito = "🔴 Crítico (Prejuízo Operacional)"
    elif (lpa is not None and lpa <= 0) and trilha != "FINANCEIRO":
        veredito = "🔴 Crítico (Prejuízo Operacional)"
    elif vpa is not None and float(vpa) <= 0:
        veredito = "🔴 Crítico (Destruição de Capital)"
    elif roe is not None and roe <= 0:
        veredito = "🔴 Crítico (Destruição de Capital)"
    elif div_liq_efetiva is not None and div_liq_efetiva > 4.5 and trilha in ("CONCESSOES_UTILITIES", "GERAL_VAREJO_TECH_IND") and not (eh_transmissora and div_liq_fco is not None and div_liq_fco <= 4.5):
        veredito = "🔴 Crítico (Alavancagem Perigosa)"
    elif news_tem_rj:
        veredito = "🔴 Crítico (Risco de Falência/RJ)"
    elif (ifr_14 is not None and ifr_14 >= 70.0) or (preco_sobrepreco is not None and cot > 0.0 and cot > float(preco_sobrepreco)):
        veredito = "🟣 Esticado (Alerta Topo/Sobrepreço)"
    elif score_lp >= 70.0 and score_cp < 40.0:
        veredito = "🟠 Indeciso (Aguardar Estabilização Técnica)"
    elif score_lp < 50.0 and score_cp >= 70.0:
        veredito = "🟠 Indeciso (Rali Sem Fundamento)"
    elif news_score <= -4.0:
        veredito = "🟠 Indeciso (Pressão de Notícias Negativas)"
    elif (
        score_geral >= 72.0
        and score_lp >= 70.0
        and (ms_consolidada is not None and ms_consolidada > 10.0)
        and (preco_teto_modelo is None or cot <= float(preco_teto_modelo))
    ):
        veredito = "🟢 Excelente (Forte Atratividade)"
    elif score_geral >= 60.0 and score_lp >= 60.0:
        if pvp is not None and 0.0 < pvp <= 0.95:
            veredito = "🔵 Bom (Desconto Patrimonial Real)"
        elif dy_12m >= 7.5:
            veredito = "🔵 Bom (Foco em Renda Passiva)"
        elif roe is not None and roe >= 16.0 and roic is not None and roic >= 12.0:
            veredito = "🔵 Bom (Empresa de Alta Eficiência)"
        else:
            veredito = "🔵 Bom (Retorno Equilibrado)"
    else:
        veredito = "🟡 Regular (Aguardar Melhor Ponto)"

    # === 7) MOTIVOS EXPLICATIVOS ===
    motivos = []
    if eh_value_trap:
        motivos.append(f"⚠️ Trava Anti-Armadilha (teto LP 50): {', '.join(armadilha_motivos)}")
    if ms_consolidada is not None:
        if ms_consolidada > 15:
            motivos.append(f"forte desconto consolidado ({ms_consolidada:+.1f}%)")
        elif ms_consolidada > 0:
            motivos.append(f"margem de segurança consolidada positiva ({ms_consolidada:+.1f}%)")
        else:
            motivos.append(f"negociada acima do preço justo consolidado ({ms_consolidada:+.1f}%)")
    if n_metodos == 1:
        motivos.append("cobertura limitada (apenas 1 método independente)")
    elif n_metodos == 2:
        motivos.append("cobertura parcial (2 métodos independentes)")
    if dy_12m <= 0.0 and dpa_med_5a <= 0.0 and anos_hist <= 0:
        motivos.append("sem histórico de dividendos (DY 0%)")
    elif dy_12m >= 7.5:
        motivos.append(f"DY atrativo ({fmt_num(dy_12m, 1)}%)")
    if pvp is not None:
        if pvp <= 0.95:
            motivos.append(f"P/VP descontado ({fmt_num(pvp)})")
        elif pvp > 1.8:
            motivos.append(f"P/VP esticado ({fmt_num(pvp)})")
    if roe is not None:
        if roe >= 16:
            motivos.append(f"ROE forte ({fmt_num(roe, 1)}%)")
        elif 0 <= roe < 8:
            motivos.append(f"ROE baixo ({fmt_num(roe, 1)}%)")
    if ifr_14 is not None:
        if trava_ifr_mm200:
            motivos.append(f"IFR {fmt_num(ifr_14, 1)} travado (máx 12 pts) abaixo da MM200")
        elif 38.0 <= ifr_14 <= 50.0:
            motivos.append(f"IFR em ponto técnico atrativo ({fmt_num(ifr_14, 1)})")
        elif ifr_14 >= 70.0:
            motivos.append(f"IFR sobrecomprado ({fmt_num(ifr_14, 1)})")
    if news_resumo != "⚪ Neutro":
        motivos.append(f"notícias 30d: {news_resumo}")

    return {
        "score_lp": score_lp,
        "score_cp": score_cp,
        "score_geral": score_geral,
        "avg_ms": ms_consolidada,
        "pt_justo_consolidado": pt_justo_consolidado,
        "motivos": motivos,
        "veredito": veredito,
        "eh_value_trap": eh_value_trap,
        "eh_utilities": eh_utilities,
        "eh_ciclica": eh_ciclica,
        "trilha": trilha,
        "preco_teto_modelo": preco_teto_modelo,
        "preco_sobrepreco": preco_sobrepreco,
        "detalhes": {
            "trilha": trilha,
            "pts_val_lp": round(pts_val_lp, 1),
            "pts_rent_lp": round(pts_rent_lp, 1),
            "pts_saude_lp": round(pts_saude_lp, 1),
            "pts_news_lp": round(pts_news_lp, 1),
            "pts_medias_cp": round(pts_medias, 1),
            "pts_ifr_cp": round(pts_ifr, 1),
            "pts_vol_cp": round(pts_vol, 1),
            "pts_ibov_cp": round(pts_ibov, 1),
            "pts_news_cp": round(pts_news_cp, 1),
            "trava_ifr_mm200": trava_ifr_mm200,
            "trava_vol_dist": trava_vol_dist,
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
    slot_copiar_ia = st.empty()

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

yield_bazin_din = buscar_yield_exigido_bazin()
TRANSMISSORAS_B3 = {"TAEE11", "TAEE3", "TAEE4", "ISAE4", "ISAE3", "TRPL4", "TRPL3", "ALUP11", "ALUP3", "ALUP4"}

preliminares = []
for a in ativos_filtrados:
    setor_of_pre = mapa_setores_ativos.get(a["ticker"], "") or mapa_fin_seg.get(a["ticker"], "")
    trilha_pre = mapear_trilha(setor_of_pre)
    roe_pre = a.get("roe")
    lpa_pre = a.get("lpa")
    vpa_pre = a.get("vpa")
    cot_pre = float(a.get("cotacao") or 0.0)
    pl_pre = (cot_pre / lpa_pre) if (cot_pre > 0 and lpa_pre is not None and lpa_pre > 0) else None
    pvp_pre = (cot_pre / vpa_pre) if (cot_pre > 0 and vpa_pre is not None and vpa_pre > 0) else None
    a_pre = {
        **a,
        "pl": pl_pre,
        "pvp": pvp_pre,
        "setor_nome": setor_of_pre,
        "setor_oficial": setor_of_pre,
        "trilha": trilha_pre,
        "eh_banco_seg": (trilha_pre == "FINANCEIRO") or (a["ticker"] in mapa_fin_seg),
        "eh_transmissora": a["ticker"] in TRANSMISSORAS_B3,
    }
    pt_bazin = a["dpa_12m"] / yield_bazin_din if a["dpa_12m"] > 0 else None
    if lpa_pre and vpa_pre and lpa_pre > 0 and vpa_pre > 0:
        f_roe_p = max(0.40, min(1.50, float(roe_pre) / 14.0)) if roe_pre is not None else 1.0
        graham = math.sqrt(22.5 * lpa_pre * (vpa_pre * f_roe_p))
    else:
        graham = None
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
    ibov_ret_30d_global = buscar_ret_ibov_30d()

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

    # Recálculo ao vivo: P/L = None se LPA <= 0; P/VP = None se VPA <= 0
    if lpa is not None:
        pl = (cot / float(lpa)) if (cot > 0 and float(lpa) > 0.0) else None
    elif pl_i10 is not None and float(pl_i10) > 0 and cot > 0 and cot_i10 and cot_i10 > 0:
        pl = pl_i10 * (cot / cot_i10)
    else:
        pl = a.get("pl") if (a.get("pl") is not None and float(a.get("pl")) > 0) else None

    if vpa is not None:
        pvp = (cot / float(vpa)) if (cot > 0 and float(vpa) > 0.0) else None
    elif pvp_i10 is not None and float(pvp_i10) > 0 and cot > 0 and cot_i10 and cot_i10 > 0:
        pvp = pvp_i10 * (cot / cot_i10)
    else:
        pvp = a.get("pvp") if (a.get("pvp") is not None and float(a.get("pvp")) > 0) else None

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
    dpa_base = min(float(dpa_12m), float(dpa_med_6a) * 1.25) if (dpa_12m and dpa_12m > 0 and dpa_med_6a and dpa_med_6a > 0) else float(dpa_12m or 0.0)

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

    # Bazin Dinâmico (Yield exigido entre 6% e 7,5%)
    pt_med = (dpa_med_6a / yield_bazin_din) if (dpa_med_6a and dpa_med_6a > 0) else None
    pt_proj = (dpa_proj / yield_bazin_din) if (dpa_proj and dpa_proj > 0) else None
    pt_bazin = (dpa_base / yield_bazin_din) if dpa_base > 0 else None

    # Graham Modernizado (Ajustado pelo ROE, Ke = 14%)
    if lpa and vpa and float(lpa) > 0 and float(vpa) > 0:
        fator_roe_g = max(0.40, min(1.50, float(roe) / 14.0)) if roe is not None else 1.0
        graham = math.sqrt(22.5 * float(lpa) * (float(vpa) * fator_roe_g))
    else:
        graham = None

    setor_oficial_t = mapa_setores_ativos.get(t, "") or mapa_fin_seg.get(t, "")
    setor_exib_t = SETOR_CURTO.get(setor_oficial_t, setor_oficial_t)
    trilha_t = mapear_trilha(setor_oficial_t)
    if t in mapa_fin_seg:
        trilha_t = "FINANCEIRO"
    eh_banco_seg = (trilha_t == "FINANCEIRO")
    eh_utilities = (trilha_t == "CONCESSOES_UTILITIES")
    eh_ciclica = (trilha_t == "COMMODITIES_CICLICAS")
    eh_transmissora = (t in TRANSMISSORAS_B3) or ("transmiss" in _norm_txt(setor_oficial_t))

    a_merged = dict(a)
    for k_base, k_i10 in (
        ("roic", "roic_i10"),
        ("marg_bruta", "marg_bruta_i10"),
        ("marg_liq", "marg_liq_i10"),
        ("marg_ebit", "marg_ebit_i10"),
        ("ev_ebitda", "ev_ebitda_i10"),
        ("ev_ebit", "ev_ebit_i10"),
        ("liq_corr", "liq_corr_i10"),
        ("div_brut_patrim", "div_brut_patrim_i10"),
        ("cresc_rec_5a", "cresc_rec_5a_i10"),
        ("cresc_lucro_5a", "cresc_lucro_5a_i10"),
        ("div_liq_ebitda", "div_liq_ebitda_i10"),
    ):
        if i10_info.get(k_i10) is not None:
            a_merged[k_base] = i10_info[k_i10]

    div_liq_ebitda = a_merged.get("div_liq_ebitda") if a_merged.get("div_liq_ebitda") is not None else yf_info.get("div_liq_ebitda_yf")
    div_liq_fco = yf_info.get("div_liq_fco_yf")
    cresc_lucro_5a = a_merged.get("cresc_lucro_5a") if a_merged.get("cresc_lucro_5a") is not None else yf_info.get("cresc_lucro_yf")
    marg_bruta = a_merged.get("marg_bruta") if a_merged.get("marg_bruta") is not None else yf_info.get("marg_bruta_yf")
    ev_eb_val = a_merged.get("ev_ebitda")
    div_liq_mkt_ratio = yf_info.get("div_liq_mktcap_ratio")

    # Método C: Múltiplo Justo Operacional Setorial
    pt_mult_justo = None
    if eh_banco_seg:
        if vpa is not None and float(vpa) > 0:
            pvp_justo_gordon = max(0.60, min(2.00, (float(roe) - 5.0) / 9.0)) if roe is not None else 1.0
            pt_mult_justo = float(vpa) * pvp_justo_gordon
    elif trilha_t in ("CONCESSOES_UTILITIES", "COMMODITIES_CICLICAS"):
        if cot > 0 and ev_eb_val is not None and float(ev_eb_val) > 0:
            mult_alvo = 7.0 if eh_utilities else 4.0
            div_liq_acao = None
            if div_liq_mkt_ratio is not None:
                div_liq_acao = cot * float(div_liq_mkt_ratio)
            elif div_liq_ebitda is not None and (float(ev_eb_val) - float(div_liq_ebitda)) > 0.25:
                ebitda_acao_est = cot / (float(ev_eb_val) - float(div_liq_ebitda))
                div_liq_acao = ebitda_acao_est * float(div_liq_ebitda)
            if div_liq_acao is not None:
                ev_acao_atual = cot + div_liq_acao
                if ev_acao_atual > 0:
                    ebitda_acao = ev_acao_atual / float(ev_eb_val)
                    pt_ev_calc = (mult_alvo * ebitda_acao) - div_liq_acao
                    pt_mult_justo = max(0.0, pt_ev_calc) if pt_ev_calc > 0 else None
            else:
                pt_mult_justo = cot * (mult_alvo / float(ev_eb_val))
    else:
        if lpa is not None and float(lpa) > 0:
            cresc_peg = cresc_lucro_5a if cresc_lucro_5a is not None else (a_merged.get("cresc_rec_5a") if a_merged.get("cresc_rec_5a") is not None else 5.0)
            pl_justo_peg = max(7.0, min(18.0, 8.0 + (0.5 * float(cresc_peg))))
            pt_mult_justo = float(lpa) * pl_justo_peg

    ret_30d_a = yf_info.get("ret_30d_pct")
    forca_rel_ibov_30d = (ret_30d_a - ibov_ret_30d_global) if (ret_30d_a is not None and ibov_ret_30d_global is not None) else None

    item = {
        **a_merged,
        "cotacao": cot, "nome": nome, "setor_nome": setor_exib_t, "setor_oficial": setor_oficial_t,
        "trilha": trilha_t, "eh_banco_seg": eh_banco_seg, "eh_utilities": eh_utilities,
        "eh_ciclica": eh_ciclica, "eh_transmissora": eh_transmissora,
        "pl": pl, "pvp": pvp, "lpa": lpa, "vpa": vpa, "roe": roe,
        "marg_bruta": marg_bruta,
        "div_liq_ebitda": div_liq_ebitda,
        "div_liq_fco": div_liq_fco,
        "cresc_lucro_5a": cresc_lucro_5a,
        "fcf_yield": yf_info.get("fcf_yield_yf"),
        "dpa_12m": dpa_12m, "dy_12m": dy_12m,
        "dpa_med_6a": dpa_med_6a, "dpa_base": dpa_base, "anos_hist": anos_hist, "dpa_proj": dpa_proj,
        "pt_med": pt_med, "pt_proj": pt_proj, "pt_bazin": pt_bazin, "graham": graham,
        "pt_mult_justo": pt_mult_justo,
        "yield_exigido_bazin": yield_bazin_din * 100.0,
        "logo_i10": i10_info.get("logo_i10", ""),
        "var_dia_pct": i10_info.get("var_dia_i10") if i10_info.get("var_dia_i10") is not None else yf_info.get("var_dia_pct"),
        "ret_5d_pct": yf_info.get("ret_5d_pct"),
        "ret_30d_pct": ret_30d_a,
        "forca_rel_ibov_30d": forca_rel_ibov_30d,
        "ifr_14": yf_info.get("ifr_14"),
        "mm20": yf_info.get("mm20"),
        "mm50": yf_info.get("mm50"),
        "mm200": yf_info.get("mm200"),
        "mm20_incl_pos": yf_info.get("mm20_incl_pos"),
        "dist_mm20_pct": yf_info.get("dist_mm20_pct"),
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
    item["pt_justo_consolidado"] = res_score["pt_justo_consolidado"]
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
            "🔵 Bom (Desc. Patr. / Renda / Eficiência / Equil.)",
            "🟣 Esticado (Alerta Topo/Sobrepreço)",
            "🟠 Indeciso (Estabilização / Rali / Notícias)",
            "🟡 Regular (Aguardar Melhor Ponto)",
            "🔴 Crítico (Prejuízo / Capital / Alavancagem / RJ)",
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

        relatorio_ia_txt = gerar_relatorio_auditoria_ia(
            resultados_tab,
            {
                "modo_ativo": modo_score_lbl,
                "listas": filtro_listas,
                "setores": filtro_setores,
                "liq": liq_label,
                "vereditos": filtro_vereditos,
                "busca": busca_tickers.strip(),
            },
        )
        _payload_ia_js = (
            json.dumps(relatorio_ia_txt, ensure_ascii=False)
            .replace("</", "<\\/")
            .replace("\u2028", "\\u2028")
            .replace("\u2029", "\\u2029")
        )
        _html_bolinha_ia = f"""
        <!DOCTYPE html>
        <html>
        <body style="margin:0;padding:0;background:transparent;overflow:hidden;font-family:system-ui,-apple-system,sans-serif;">
        <div style="display:flex; flex-direction:column; align-items:center; justify-content:center; gap:4px; margin-top:2px;">
          <button id="btn-copiar-ia-b3" type="button"
            title="Copiar análise completa dos {len(resultados_tab)} ativos filtrados (Geral, LP e CP) para auditar em IA"
            style="width:36px; height:36px; border-radius:50%; border:1.5px solid rgba(96,165,250,0.65);
                   background:linear-gradient(135deg, rgba(59,130,246,0.28), rgba(37,99,235,0.45));
                   color:#ffffff; font-size:16px; cursor:pointer; display:inline-flex;
                   align-items:center; justify-content:center; box-shadow:0 2px 8px rgba(0,0,0,0.35);
                   transition:transform 0.12s ease, background 0.15s ease, border-color 0.15s ease;">
            🤖
          </button>
          <span id="lbl-copiar-ia-b3" style="font-size:11px; color:#4ade80; font-weight:600; min-height:14px; text-align:center;"></span>
        </div>
        <script>
        (function() {{
          const txt = {_payload_ia_js};
          const btn = document.getElementById("btn-copiar-ia-b3");
          const lbl = document.getElementById("lbl-copiar-ia-b3");
          if (!btn) return;
          btn.addEventListener("click", async function() {{
            let ok = false;
            try {{
              if (navigator && navigator.clipboard && navigator.clipboard.writeText) {{
                await navigator.clipboard.writeText(txt);
                ok = true;
              }}
            }} catch (e1) {{}}
            if (!ok) {{
              try {{
                const ta = document.createElement("textarea");
                ta.value = txt;
                ta.setAttribute("readonly", "");
                ta.style.position = "fixed";
                ta.style.left = "-9999px";
                ta.style.top = "0";
                document.body.appendChild(ta);
                ta.focus();
                ta.select();
                ta.setSelectionRange(0, txt.length);
                ok = document.execCommand("copy");
                document.body.removeChild(ta);
              }} catch (e2) {{}}
            }}
            if (!ok) {{
              try {{
                if (window.parent && window.parent.navigator && window.parent.navigator.clipboard && window.parent.navigator.clipboard.writeText) {{
                  await window.parent.navigator.clipboard.writeText(txt);
                  ok = true;
                }}
              }} catch (e3) {{}}
            }}
            if (!ok) {{
              try {{
                const pDoc = window.parent && window.parent.document;
                if (pDoc) {{
                  const taP = pDoc.createElement("textarea");
                  taP.value = txt;
                  taP.style.position = "fixed";
                  taP.style.left = "-9999px";
                  pDoc.body.appendChild(taP);
                  taP.focus();
                  taP.select();
                  ok = pDoc.execCommand("copy");
                  pDoc.body.removeChild(taP);
                }}
              }} catch (e4) {{}}
            }}
            if (ok) {{
              btn.textContent = "✓";
              btn.style.background = "linear-gradient(135deg, #16a34a, #22c55e)";
              btn.style.borderColor = "#4ade80";
              if (lbl) {{
                lbl.style.color = "#4ade80";
                lbl.textContent = "Copiado ({len(resultados_tab)} ativos)!";
              }}
              setTimeout(function() {{
                btn.textContent = "🤖";
                btn.style.background = "linear-gradient(135deg, rgba(59,130,246,0.28), rgba(37,99,235,0.45))";
                btn.style.borderColor = "rgba(96,165,250,0.65)";
                if (lbl) lbl.textContent = "";
              }}, 2800);
            }} else if (lbl) {{
              lbl.style.color = "#f87171";
              lbl.textContent = "Erro ao copiar";
            }}
          }});
        }})();
        </script>
        </body>
        </html>
        """
        with slot_copiar_ia:
            components.html(_html_bolinha_ia, height=64)

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
            "div[data-testid='stElementContainer']:has(.raiox-table-host),"
            "div.element-container:has(.raiox-table-host),"
            "div[data-testid='stElementContainer']:has(.raiox-current-marker),"
            "div.element-container:has(.raiox-current-marker){"
            "display:none!important;margin:0!important;padding:0!important;height:0!important;}"
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
            ".val-table th.col-sticky-0,.val-table td.col-sticky-0,.val-table th.col-sticky-1,.val-table td.col-sticky-1{"
            "position:sticky!important;background-clip:padding-box!important;}"
            ".val-table th.col-sticky-0,.val-table th.col-sticky-1{"
            "z-index:25!important;background-color:var(--val-sticky-bg,var(--background-color,#0e1117))!important;"
            "background-image:linear-gradient(rgba(128,128,128,0.18),rgba(128,128,128,0.18))!important;}"
            ".val-table td.col-sticky-0,.val-table td.col-sticky-1{"
            "z-index:15!important;background-color:var(--val-sticky-bg,var(--background-color,#0e1117))!important;}"
            ".val-table tr:hover td.col-sticky-0,.val-table tr:hover td.col-sticky-1{"
            "background-color:var(--val-sticky-bg,var(--background-color,#0e1117))!important;"
            "background-image:linear-gradient(rgba(128,128,128,0.08),rgba(128,128,128,0.08))!important;}"
            ".val-table tr.raiox-active-row td.col-sticky-0,.val-table tr.raiox-active-row td.col-sticky-1{"
            "background-color:var(--val-sticky-bg,var(--background-color,#0e1117))!important;"
            "background-image:linear-gradient(rgba(59,130,246,0.14),rgba(59,130,246,0.14))!important;}"
            ".val-table th.col-sticky-1,.val-table td.col-sticky-1{"
            "box-shadow:3px 0 8px rgba(0,0,0,0.32)!important;}"
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
                    logo_c1 = html_logo_ativo(lider_atr["ticker"], lider_atr.get("logo_i10", ""), size=46, radius=9, bg_monogram="rgba(16,185,129,0.22)")
                    st.markdown(
                        "<div style='min-height:164px; border-radius:12px; padding:14px 16px; "
                        "border:1px solid rgba(16,185,129,0.55); "
                        "background:linear-gradient(145deg, rgba(16,185,129,0.16) 0%, rgba(10,22,18,0.90) 58%, rgba(7,14,11,0.96) 100%); "
                        "display:flex; flex-direction:column; justify-content:space-between; gap:10px;'>"
                        "<div style='display:flex; justify-content:space-between; align-items:center; gap:6px; flex-wrap:nowrap;'>"
                        "<div style='display:flex; align-items:center; gap:7px; min-width:0;'>"
                        "<span style='font-size:16px; line-height:1;'>🏆</span>"
                        "<span style='background:rgba(16,185,129,0.22); border:1px solid rgba(16,185,129,0.45); color:#34d399; "
                        "border-radius:999px; padding:2px 9px; font-size:11px; font-weight:700; white-space:nowrap; overflow:hidden; text-overflow:ellipsis;'>Líder de Atratividade</span>"
                        "</div>"
                        f"<div style='flex-shrink:0;'>{badge_veredito_html(lider_atr.get('veredito', ''))}</div>"
                        "</div>"
                        "<div style='display:flex; justify-content:space-between; align-items:center; gap:10px;'>"
                        "<div style='min-width:0;'>"
                        f"<div style='font-size:21px; font-weight:800; color:#f8fafc; line-height:1.15;'>{lider_atr['ticker']}</div>"
                        f"<div style='font-size:12px; color:rgba(226,232,240,0.75); white-space:nowrap; overflow:hidden; text-overflow:ellipsis; margin-top:2px;' title='{html.escape(lider_atr['nome'])}'>{html.escape(lider_atr['nome'])}</div>"
                        "</div>"
                        f"{logo_c1}"
                        "</div>"
                        "<div style='display:grid; grid-template-columns:repeat(2,minmax(0,1fr)); padding-top:4px;'>"
                        "<div style='border-right:1px solid rgba(255,255,255,0.12); padding-right:10px;'>"
                        "<div style='font-size:11px; color:rgba(226,232,240,0.68);'>📈 Cotação</div>"
                        f"<div style='font-size:16px; font-weight:800; color:#f8fafc; margin-top:2px;'>R$ {fmt_num(lider_atr['cotacao'])}</div>"
                        "</div>"
                        "<div style='padding-left:12px;'>"
                        "<div style='font-size:11px; color:rgba(226,232,240,0.68);'>⭐ Score Ativo</div>"
                        f"<div style='font-size:16px; font-weight:800; color:#34d399; margin-top:2px;'>{fmt_num(lider_atr['score_ativo'], 1)}/100</div>"
                        "</div>"
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
                    if cands_dy:
                        top_dy = max(cands_dy, key=lambda x: float(x["dy_12m"]))
                        bz_dy = top_dy.get("pt_bazin")
                        bz_txt = f"R$ {fmt_num(bz_dy)}" if (bz_dy and bz_dy > 0) else "—"
                        logo_c2 = html_logo_ativo(top_dy["ticker"], top_dy.get("logo_i10", ""), size=46, radius=9, bg_monogram="rgba(245,158,11,0.22)")
                        st.markdown(
                            "<div style='min-height:164px; border-radius:12px; padding:14px 16px; "
                            "border:1px solid rgba(245,158,11,0.55); "
                            "background:linear-gradient(145deg, rgba(245,158,11,0.16) 0%, rgba(24,18,8,0.90) 58%, rgba(15,11,6,0.96) 100%); "
                            "display:flex; flex-direction:column; justify-content:space-between; gap:10px;'>"
                            "<div style='display:flex; align-items:center; gap:7px;'>"
                            "<span style='font-size:16px; line-height:1;'>🪙</span>"
                            "<span style='background:rgba(245,158,11,0.22); border:1px solid rgba(245,158,11,0.45); color:#fbbf24; "
                            "border-radius:999px; padding:2px 9px; font-size:11px; font-weight:700; white-space:nowrap;'>Maior DY Sustentável</span>"
                            "</div>"
                            "<div style='display:flex; justify-content:space-between; align-items:center; gap:10px;'>"
                            "<div style='min-width:0;'>"
                            f"<div style='font-size:21px; font-weight:800; color:#f8fafc; line-height:1.15;'>{top_dy['ticker']}</div>"
                            f"<div style='font-size:12px; color:rgba(226,232,240,0.75); white-space:nowrap; overflow:hidden; text-overflow:ellipsis; margin-top:2px;' title='{html.escape(top_dy['nome'])}'>{html.escape(top_dy['nome'])}</div>"
                            "</div>"
                            f"{logo_c2}"
                            "</div>"
                            "<div style='display:grid; grid-template-columns:repeat(3,minmax(0,1fr)); padding-top:4px;'>"
                            "<div style='border-right:1px solid rgba(255,255,255,0.12); padding-right:6px;'>"
                            "<div style='font-size:11px; color:rgba(226,232,240,0.68); white-space:nowrap;'>📈 Cotação</div>"
                            f"<div style='font-size:14.5px; font-weight:800; color:#f8fafc; margin-top:2px; white-space:nowrap;'>R$ {fmt_num(top_dy['cotacao'])}</div>"
                            "</div>"
                            "<div style='border-right:1px solid rgba(255,255,255,0.12); padding:0 6px;'>"
                            "<div style='font-size:11px; color:rgba(226,232,240,0.68); white-space:nowrap;'>DY 12 meses</div>"
                            f"<div style='font-size:14.5px; font-weight:800; color:#fbbf24; margin-top:2px; white-space:nowrap;'>{fmt_num(top_dy['dy_12m'], 2)}%</div>"
                            "</div>"
                            "<div style='padding-left:6px;'>"
                            "<div style='font-size:11px; color:rgba(226,232,240,0.68); white-space:nowrap;'>🎯 Teto Bazin</div>"
                            f"<div style='font-size:14.5px; font-weight:800; color:#f8fafc; margin-top:2px; white-space:nowrap;'>{bz_txt}</div>"
                            "</div>"
                            "</div>"
                            "</div>",
                            unsafe_allow_html=True,
                        )
                    else:
                        st.markdown(
                            "<div style='min-height:164px; border-radius:12px; padding:14px 16px; "
                            "border:1px solid rgba(245,158,11,0.45); "
                            "background:linear-gradient(145deg, rgba(245,158,11,0.12) 0%, rgba(24,18,8,0.90) 60%, rgba(15,11,6,0.96) 100%); "
                            "display:flex; flex-direction:column; justify-content:space-between;'>"
                            "<div style='display:flex; align-items:center; gap:7px;'><span style='font-size:16px;'>🪙</span>"
                            "<span style='background:rgba(245,158,11,0.22); border:1px solid rgba(245,158,11,0.45); color:#fbbf24; border-radius:999px; padding:2px 9px; font-size:11px; font-weight:700;'>Maior DY Sustentável</span></div>"
                            "<div style='font-size:12px; opacity:0.78;'>Sem ativo elegível com ROE &gt; 10% e DY &gt; 0% neste filtro.</div>"
                            "<div></div></div>",
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
                    if cands_ifr:
                        top_ifr = min(cands_ifr, key=lambda x: float(x["ifr_14"]))
                        d200_i = top_ifr.get("dist_mm200_pct")
                        d200_s = f"{d200_i:+.1f}%" if d200_i is not None else "—"
                        cor_d200 = "#4ade80" if (d200_i is not None and d200_i >= 0) else "#fb923c"
                        logo_c3 = html_logo_ativo(top_ifr["ticker"], top_ifr.get("logo_i10", ""), size=46, radius=9, bg_monogram="rgba(168,85,247,0.22)")
                        st.markdown(
                            "<div style='min-height:164px; border-radius:12px; padding:14px 16px; "
                            "border:1px solid rgba(168,85,247,0.58); "
                            "background:linear-gradient(145deg, rgba(168,85,247,0.16) 0%, rgba(20,12,28,0.90) 58%, rgba(13,9,19,0.96) 100%); "
                            "display:flex; flex-direction:column; justify-content:space-between; gap:10px;'>"
                            "<div style='display:flex; align-items:center; gap:7px;'>"
                            "<span style='font-size:16px; line-height:1;'>⚡</span>"
                            "<span style='background:rgba(168,85,247,0.22); border:1px solid rgba(168,85,247,0.48); color:#c084fc; "
                            "border-radius:999px; padding:2px 9px; font-size:11px; font-weight:700; white-space:nowrap;'>Oportunidade Técnica</span>"
                            "</div>"
                            "<div style='display:flex; justify-content:space-between; align-items:center; gap:10px;'>"
                            "<div style='min-width:0;'>"
                            f"<div style='font-size:21px; font-weight:800; color:#f8fafc; line-height:1.15;'>{top_ifr['ticker']}</div>"
                            f"<div style='font-size:12px; color:rgba(226,232,240,0.75); white-space:nowrap; overflow:hidden; text-overflow:ellipsis; margin-top:2px;' title='{html.escape(top_ifr['nome'])}'>{html.escape(top_ifr['nome'])}</div>"
                            "</div>"
                            f"{logo_c3}"
                            "</div>"
                            "<div style='display:grid; grid-template-columns:repeat(3,minmax(0,1fr)); padding-top:4px;'>"
                            "<div style='border-right:1px solid rgba(255,255,255,0.12); padding-right:6px;'>"
                            "<div style='font-size:11px; color:rgba(226,232,240,0.68); white-space:nowrap;'>📈 Cotação</div>"
                            f"<div style='font-size:14.5px; font-weight:800; color:#f8fafc; margin-top:2px; white-space:nowrap;'>R$ {fmt_num(top_ifr['cotacao'])}</div>"
                            "</div>"
                            "<div style='border-right:1px solid rgba(255,255,255,0.12); padding:0 6px;'>"
                            "<div style='font-size:11px; color:rgba(226,232,240,0.68); white-space:nowrap;'>📊 IFR (14d)</div>"
                            f"<div style='font-size:14.5px; font-weight:800; color:#f8fafc; margin-top:2px; white-space:nowrap;'>{fmt_num(top_ifr['ifr_14'], 1)}</div>"
                            "</div>"
                            "<div style='padding-left:6px;'>"
                            "<div style='font-size:11px; color:rgba(226,232,240,0.68); white-space:nowrap;'>📉 Dist. MM200</div>"
                            f"<div style='font-size:14.5px; font-weight:800; color:{cor_d200}; margin-top:2px; white-space:nowrap;'>{d200_s}</div>"
                            "</div>"
                            "</div>"
                            "</div>",
                            unsafe_allow_html=True,
                        )
                    else:
                        st.markdown(
                            "<div style='min-height:164px; border-radius:12px; padding:14px 16px; "
                            "border:1px solid rgba(168,85,247,0.45); "
                            "background:linear-gradient(145deg, rgba(168,85,247,0.12) 0%, rgba(20,12,28,0.90) 60%, rgba(13,9,19,0.96) 100%); "
                            "display:flex; flex-direction:column; justify-content:space-between;'>"
                            "<div style='display:flex; align-items:center; gap:7px;'><span style='font-size:16px;'>⚡</span>"
                            "<span style='background:rgba(168,85,247,0.22); border:1px solid rgba(168,85,247,0.48); color:#c084fc; border-radius:999px; padding:2px 9px; font-size:11px; font-weight:700;'>Oportunidade Técnica</span></div>"
                            "<div style='font-size:12px; opacity:0.78;'>Indicadores técnicos não carregados para este filtro.</div>"
                            "<div></div></div>",
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
                    if cands_gr:
                        ms_best, top_gr = max(cands_gr, key=lambda pair: pair[0])
                        logo_c4 = html_logo_ativo(top_gr["ticker"], top_gr.get("logo_i10", ""), size=46, radius=9, bg_monogram="rgba(56,189,248,0.22)")
                        st.markdown(
                            "<div style='min-height:164px; border-radius:12px; padding:14px 16px; "
                            "border:1px solid rgba(56,189,248,0.58); "
                            "background:linear-gradient(145deg, rgba(56,189,248,0.16) 0%, rgba(10,20,30,0.90) 58%, rgba(7,13,20,0.96) 100%); "
                            "display:flex; flex-direction:column; justify-content:space-between; gap:10px;'>"
                            "<div style='display:flex; align-items:center; gap:7px;'>"
                            "<span style='font-size:16px; line-height:1;'>💎</span>"
                            "<span style='background:rgba(56,189,248,0.20); border:1px solid rgba(56,189,248,0.45); color:#38bdf8; "
                            "border-radius:999px; padding:2px 9px; font-size:11px; font-weight:700; white-space:nowrap;'>Maior Desconto Graham</span>"
                            "</div>"
                            "<div style='display:flex; justify-content:space-between; align-items:center; gap:10px;'>"
                            "<div style='min-width:0;'>"
                            f"<div style='font-size:21px; font-weight:800; color:#f8fafc; line-height:1.15;'>{top_gr['ticker']}</div>"
                            f"<div style='font-size:12px; color:rgba(226,232,240,0.75); white-space:nowrap; overflow:hidden; text-overflow:ellipsis; margin-top:2px;' title='{html.escape(top_gr['nome'])}'>{html.escape(top_gr['nome'])}</div>"
                            "</div>"
                            f"{logo_c4}"
                            "</div>"
                            "<div style='display:grid; grid-template-columns:repeat(3,minmax(0,1fr)); padding-top:4px;'>"
                            "<div style='border-right:1px solid rgba(255,255,255,0.12); padding-right:6px;'>"
                            "<div style='font-size:11px; color:rgba(226,232,240,0.68); white-space:nowrap;'>📈 Cotação</div>"
                            f"<div style='font-size:14.5px; font-weight:800; color:#f8fafc; margin-top:2px; white-space:nowrap;'>R$ {fmt_num(top_gr['cotacao'])}</div>"
                            "</div>"
                            "<div style='border-right:1px solid rgba(255,255,255,0.12); padding:0 6px;'>"
                            "<div style='font-size:11px; color:rgba(226,232,240,0.68); white-space:nowrap;'>🏛️ Graham</div>"
                            f"<div style='font-size:14.5px; font-weight:800; color:#f8fafc; margin-top:2px; white-space:nowrap;'>R$ {fmt_num(top_gr['graham'])}</div>"
                            "</div>"
                            "<div style='padding-left:6px;'>"
                            "<div style='font-size:11px; color:rgba(226,232,240,0.68); white-space:nowrap;'>✳️ Margem</div>"
                            f"<div style='font-size:14.5px; font-weight:800; color:#4ade80; margin-top:2px; white-space:nowrap;'>+{fmt_num(ms_best, 1)}%</div>"
                            "</div>"
                            "</div>"
                            "</div>",
                            unsafe_allow_html=True,
                        )
                    else:
                        st.markdown(
                            "<div style='min-height:164px; border-radius:12px; padding:14px 16px; "
                            "border:1px solid rgba(56,189,248,0.45); "
                            "background:linear-gradient(145deg, rgba(56,189,248,0.12) 0%, rgba(10,20,30,0.90) 60%, rgba(7,13,20,0.96) 100%); "
                            "display:flex; flex-direction:column; justify-content:space-between;'>"
                            "<div style='display:flex; align-items:center; gap:7px;'><span style='font-size:16px;'>💎</span>"
                            "<span style='background:rgba(56,189,248,0.20); border:1px solid rgba(56,189,248,0.45); color:#38bdf8; border-radius:999px; padding:2px 9px; font-size:11px; font-weight:700;'>Maior Desconto Graham</span></div>"
                            "<div style='font-size:12px; opacity:0.78;'>Nenhum ativo abaixo do valor de Graham neste filtro.</div>"
                            "<div></div></div>",
                            unsafe_allow_html=True,
                        )
            st.markdown("<div style='height:8px;'></div>", unsafe_allow_html=True)

        with st.expander(f"📋 Tabela Comparativa ({len(resultados_tab)} ativos no filtro) — clique para minimizar/maximizar | clique em qualquer linha para abrir/fechar o Raio-X", expanded=True):
            opcoes_ordenacao = {
                "Atratividade (Score Ativo)": "score_ativo",
                "Score Geral (70% LP + 30% CP)": "score_geral",
                "Score Longo Prazo (LP)": "score_lp",
                "Score Curto Prazo (CP)": "score_cp",
                "Margem de Segurança Consolidada (%)": "avg_ms",
                "IFR (14 dias)": "ifr_14",
                "Notícias 30d (News Score)": "news_score",
                "Cotação (R$)": "cotacao",
                "Dividend Yield 12m (%)": "dy_12m",
                "P/L": "pl",
                "P/VP": "pvp",
                "ROE (%)": "roe",
                "ROIC (%)": "roic",
                "Preço Teto Med. Aparada (5a)": "pt_med",
                "Preço Teto Projetivo": "pt_proj",
                "Preço-Teto Bazin Dinâmico": "pt_bazin",
                "Preço Justo Graham Adj.": "graham",
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

            with st.container(border=True):
                st.markdown(
                    "<span class='painel-analise-host' style='display:none;'></span>"
                    "<style>"
                    "div[data-testid='stVerticalBlockBorderWrapper']:has(.painel-analise-host){"
                    "padding:10px 14px!important;}"
                    "div[data-testid='stVerticalBlock']:has(> div .painel-analise-host),"
                    "div[data-testid='stVerticalBlock']:has(> div > div .painel-analise-host){"
                    "gap:8px!important;}"
                    "div[data-testid='stElementContainer']:has(.painel-analise-host),"
                    "div[data-testid='stElementContainer']:has(.painel-modo-host),"
                    "div[data-testid='stElementContainer']:has(.painel-link-host){"
                    "display:none!important;margin:0!important;padding:0!important;height:0!important;}"
                    "div[data-testid='stHorizontalBlock']:has(.painel-modo-host) button{"
                    "border-radius:8px!important;min-height:36px!important;padding:4px 10px!important;font-size:13.5px!important;transition:all 0.15s ease!important;}"
                    "div[data-testid='stHorizontalBlock']:has(.painel-modo-host) button[kind='primary']{"
                    "background:rgba(16,185,129,0.16)!important;border:1px solid rgba(16,185,129,0.62)!important;"
                    "color:#34d399!important;font-weight:600!important;box-shadow:none!important;}"
                    "div[data-testid='stHorizontalBlock']:has(.painel-modo-host) button[kind='primary']:hover{"
                    "background:rgba(16,185,129,0.24)!important;border-color:rgba(16,185,129,0.82)!important;}"
                    "div[data-testid='stHorizontalBlock']:has(.painel-modo-host) button[kind='secondary']{"
                    "background:rgba(128,128,129,0.12)!important;border:1px solid rgba(128,128,129,0.25)!important;"
                    "color:inherit!important;font-weight:500!important;}"
                    "div[data-testid='stHorizontalBlock']:has(.painel-modo-host) button[kind='secondary']:hover{"
                    "background:rgba(128,128,129,0.20)!important;border-color:rgba(128,128,129,0.42)!important;}"
                    "div[data-testid='stColumn']:has(.painel-link-host){display:flex;justify-content:flex-end;align-items:center;}"
                    "div[data-testid='stColumn']:has(.painel-link-host) button{"
                    "background:transparent!important;border:none!important;box-shadow:none!important;"
                    "color:#60a5fa!important;padding:0px 4px!important;min-height:0!important;width:auto!important;font-size:13px!important;font-weight:500!important;}"
                    "div[data-testid='stColumn']:has(.painel-link-host) button:hover{"
                    "color:#93c5fd!important;text-decoration:underline!important;background:transparent!important;}"
                    "</style>",
                    unsafe_allow_html=True,
                )

                c_pa_tit, c_pa_dic = st.columns([3.5, 1.0], vertical_alignment="center")
                with c_pa_tit:
                    st.markdown("<div style='font-size:13.5px; font-weight:700; letter-spacing:0.5px; line-height:1.2;'>MODO DE ANÁLISE</div>", unsafe_allow_html=True)
                with c_pa_dic:
                    st.markdown("<span class='painel-link-host' style='display:none;'></span>", unsafe_allow_html=True)
                    if st.button("📖 Dicionário", key="btn_dic_tab1"):
                        modal_dicionario()

                modos_ui = [
                    ("🏆 Geral", "🏆 Geral (Melhor Compra Equilibrada)"),
                    ("🏛️ Longo Prazo", "🏛️ Longo Prazo (Fundamentos & Dividendos)"),
                    ("⚡ Curto Prazo", "⚡ Curto Prazo (Timing & Catalisadores)"),
                ]
                cols_modo_ui = st.columns(3, gap="small")
                for idx_m, (col_m, (lbl_curto_m, lbl_full_m)) in enumerate(zip(cols_modo_ui, modos_ui)):
                    with col_m:
                        if idx_m == 0:
                            st.markdown("<span class='painel-modo-host' style='display:none;'></span>", unsafe_allow_html=True)
                        eh_modo_sel = (st.session_state["tab1_modo_score_val"] == lbl_full_m)
                        if st.button(
                            lbl_curto_m,
                            key=f"btn_modo_ui_{idx_m}",
                            type="primary" if eh_modo_sel else "secondary",
                            use_container_width=True,
                        ):
                            if not eh_modo_sel:
                                st.session_state["tab1_modo_score_val"] = lbl_full_m
                                st.session_state["tab1_modo_score_tab"] = lbl_full_m
                                st.session_state["tab1_modo_score_rank"] = lbl_full_m
                                st.query_params["modo"] = lbl_full_m
                                st.rerun()

                st.markdown("<div style='margin:2px 0; border-top:1px solid rgba(128,128,128,0.22);'></div>", unsafe_allow_html=True)

                c_busca, c_ver, c_ord1, c_ord2, c_ord3 = st.columns([1.35, 1.35, 1.25, 1.05, 0.8], vertical_alignment="bottom")
                with c_busca:
                    busca_reset_id = st.session_state.get("tab1_busca_reset", 0)
                    q_url = "" if busca_reset_id > 0 else st.query_params.get("q", "")
                    busca_key = "busca_live" if busca_reset_id == 0 else f"busca_live_{busca_reset_id}"
                    if "value" in inspect.signature(st_keyup).parameters:
                        busca_tabela = st_keyup("Buscar ativo", value=q_url, placeholder="🔍 PETR, BBAS...", debounce=200, key=busca_key)
                    else:
                        busca_tabela = st_keyup("Buscar ativo", placeholder="🔍 PETR, BBAS...", debounce=200, key=busca_key)
                with c_ver:
                    st.multiselect(
                        "Veredito",
                        options=VEREDITOS_OPCOES,
                        placeholder="Todos os vereditos",
                        key="tab1_filtro_ver_tab",
                        on_change=_sync_ver_tab,
                    )
                with c_ord1:
                    col_escolhida = st.selectbox(
                        "Ordenar por",
                        ord_keys,
                        key="tab1_ord_col",
                        format_func=lambda x: x.split(" (")[0],
                    )
                with c_ord2:
                    direcao = st.selectbox(
                        "Ordem",
                        dir_opcoes,
                        key="tab1_ord_dir",
                        format_func=lambda x: x.split(" (")[0],
                    )
                with c_ord3:
                    max_linhas = st.number_input("Exibir", min_value=0, max_value=1000, step=10, key="tab1_max_linhas")

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

                c_ft_cnt, c_ft_limp = st.columns([3.0, 1.2], vertical_alignment="center")
                with c_ft_cnt:
                    st.markdown(f"<div style='font-size:13px; opacity:0.75;'>{len(exibir)} de {len(lista_tab)} ativos</div>", unsafe_allow_html=True)
                with c_ft_limp:
                    st.markdown("<span class='painel-link-host' style='display:none;'></span>", unsafe_allow_html=True)
                    if st.button("Limpar filtros ↺", key="btn_limpar_filtros_tab1"):
                        st.session_state["tab1_busca_reset"] = st.session_state.get("tab1_busca_reset", 0) + 1
                        st.session_state["tab1_filtro_ver_tab"] = []
                        st.session_state["tab1_filtro_ver_rank"] = []
                        st.session_state["tab1_filtro_veredito_val"] = []
                        st.session_state["tab1_ord_col"] = ord_keys[0]
                        st.session_state["tab1_ord_dir"] = dir_opcoes[0]
                        st.session_state["tab1_max_linhas"] = 50
                        st.query_params["ord"] = ord_keys[0]
                        st.query_params["dir"] = dir_opcoes[0]
                        st.query_params["maxl"] = "50"
                        for qp_clr in ("q", "ver"):
                            if qp_clr in st.query_params:
                                del st.query_params[qp_clr]
                        st.rerun()

            falt_i10_tab = tuple(r["ticker"] for r in exibir if r["ticker"] not in dados_i10)
            mapa_res_tab = {r["ticker"]: r for r in resultados_tab}
            if falt_i10_tab and len(falt_i10_tab) <= 60:
                if len(falt_i10_tab) <= 30:
                    falt_yf_t = tuple(tk for tk in falt_i10_tab if tk not in dados_yf)
                    if falt_yf_t:
                        dados_yf.update(buscar_yahoo_lote(falt_yf_t))
                if len(falt_i10_tab) <= 15:
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
                    def _ao_clicar_ticker_tabela():
                        raw_rx = st.session_state.get("raiox_bridge", "").strip().upper()
                        st.session_state["raiox_bridge"] = ""
                        if not raw_rx:
                            return
                        tk_clicado = raw_rx.split("|")[0].strip()
                        if not tk_clicado:
                            return
                        for _k_co in [k for k in st.session_state.keys() if k.startswith("tab1_chart_open_")]:
                            st.session_state.pop(_k_co, None)
                        if st.session_state.get("raiox_visivel", False) and st.session_state.get("raiox_ativo_sel") == tk_clicado:
                            st.session_state["raiox_visivel"] = False
                        else:
                            st.session_state["raiox_ativo_sel"] = tk_clicado
                            st.session_state["raiox_visivel"] = True

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

                        var_d = r.get("var_dia_pct")
                        if var_d is not None:
                            if var_d > 0.004:
                                cor_vd, sinal_vd = "#22c55e", "+"
                            elif var_d < -0.004:
                                cor_vd, sinal_vd = "#ef4444", ""
                            else:
                                cor_vd, sinal_vd = "#94a3b8", ""
                            var_dia_html = (
                                f"<div title='Variação no dia em relação ao fechamento anterior' "
                                f"style='flex-shrink:0; font-size:12.5px; font-weight:700; color:{cor_vd}; white-space:nowrap; text-align:right;'>"
                                f"{sinal_vd}{fmt_num(var_d, 2)}%</div>"
                            )
                        else:
                            var_dia_html = ""

                        logo_td = html_logo_ativo(r["ticker"], r.get("logo_i10", ""), size=36, radius=7)
                        linha = (
                            f"<tr{tr_cls} data-raiox-ticker='{r['ticker']}'>"
                            f"<td class='col-sticky-0' style='text-align:center;'><span class='{chk_cls}' data-comp-ticker='{r['ticker']}' role='checkbox' aria-checked='{'true' if r['ticker'] in comp_ativos else 'false'}' title='Selecionar para Comparar Ativos'></span></td>"
                            f"<td class='col-sticky-1'>"
                            f"<div style='display:flex; align-items:center; gap:10px;'>"
                            f"{logo_td}"
                            f"<div style='min-width:0;'><span style='color:#60a5fa; font-weight:700;'>{r['ticker']}</span>{estrela}<br><small style='opacity:0.88;'>{nome_esc}</small>{setor_badge}</div>"
                            f"</div>"
                            f"</td>"
                            f"<td style='text-align:center; line-height:1.35;'>"
                            f"<span style='font-weight:700;' title='Posição no Ranking e Score Ativo (0 a 100)'>{r['pos_ranking']}º · <strong>{fmt_num(score_at, 1)}</strong></span>"
                            f"<br>{badge_v}"
                            f"<br><small style='opacity:0.85; white-space:nowrap;' title='IFR 14 dias (RSI): {ifr_ic} | Notícias 30d: {html.escape(news_res_r)}'>{ifr_ic} | {news_ic}</small>"
                            f"</td>"
                            f"<td>"
                            f"<div style='display:flex; justify-content:space-between; align-items:center; gap:10px;'>"
                            f"<div style='min-width:0;'><strong>R$ {fmt_num(cot)}</strong><br><small title='Dividend Yield (12 meses): percentual pago em dividendos/JCP sobre a cotação atual'>DY: {fmt_num(r['dy_12m'])}%</small></div>"
                            f"{var_dia_html}"
                            f"</div>"
                            f"</td>"
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
                        "<th class='col-sticky-0' style='text-align:center;' title='Marque os ativos para comparar lado a lado na aba Comparar Ativos'>⚖️</th>"
                        "<th class='col-sticky-1' title='Código na B3, nome da empresa e setor de atuação'>Ticker / Empresa</th>"
                        "<th style='text-align:center;' title='Posição no Ranking, Score Ativo (0 a 100), Veredito do Modelo, IFR 14 dias e Sentimento de Notícias (30d)'>Rank / Score<br><small>Veredito | IFR | News</small></th>"
                        f"<th title='Cotação atual da ação, variação diária (%) e DY (Dividend Yield 12 meses)'>Cotação ({datetime.now(BRT).strftime('%d/%m/%Y %H:%M')}) & DY</th>"
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
                            _rx_ctx = st.container(key=f"rx_box_{ativo_escolhido}") if "key" in inspect.signature(st.container).parameters else st.container()
                            with _rx_ctx:
                                st.markdown(
                                    f"<span class='raiox-current-marker' id='raiox-current-{ativo_escolhido}' style='display:none;'></span>"
                                    "<span class='raiox-indent-host' style='display:none;'></span>",
                                    unsafe_allow_html=True,
                                )
                                item_raiox = mapa_res[ativo_escolhido]
                                render_grafico_e_tabela_ativo(
                                    ativo_escolhido,
                                    item_raiox["nome"],
                                    base_ativo=item_raiox,
                                    key_prefix="tab1",
                                    modo_score_chave=modo_score_chave,
                                    mostrar_cabecalho=False,
                                    expandir_padrao=False,
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
            const STORAGE_KEY = "painel_b3_val_col_widths_v4";

            function applyStickyBgVars() {
                const refEl = pDoc.querySelector('[data-testid="stAppViewContainer"]') || pDoc.body;
                if (!refEl) return;
                const bg = pWin.getComputedStyle(refEl).backgroundColor;
                if (bg && bg !== "rgba(0, 0, 0, 0)" && bg !== "transparent") {
                    pDoc.documentElement.style.setProperty("--val-sticky-bg", bg);
                }
            }

            function syncStickyCols(tbl, col0W) {
                if (!tbl) return;
                const w0 = Math.max(36, Math.round(col0W || 42));
                tbl.querySelectorAll(".col-sticky-0").forEach(function(el) { el.style.left = "0px"; });
                tbl.querySelectorAll(".col-sticky-1").forEach(function(el) { el.style.left = w0 + "px"; });
            }

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
                if (widthsArr.length >= 2) {
                    syncStickyCols(tbl, widthsArr[0]);
                }
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

                applyStickyBgVars();
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
                    widths = ths.map((th, i) => Math.max(i === 0 ? 42 : (i === 1 ? 235 : (i === 3 ? 185 : 54)), Math.round(th.getBoundingClientRect().width)));
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
                            if (idx === 0) {
                                syncStickyCols(topTable, newW);
                                if (bTbl) syncStickyCols(bTbl, newW);
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

                    if (e.target && e.target.closest && e.target.closest("a, button, input, select, textarea, .raiox-blocks-host, .raiox-indent-host")) return;
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
        if (pt.rawLabel !== undefined) return String(pt.rawLabel);
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
            const rawCd = Array.isArray(tr.customdata) ? tr.customdata : null;
            const rawTxts = Array.isArray(tr.text) ? tr.text : null;

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
                        let rawLabel = undefined;
                        let rawTs = undefined;
                        if (rawCd && Array.isArray(rawCd[i]) && typeof rawCd[i][0] === "string") {
                            rawLabel = rawCd[i][0];
                            if (rawCd[i].length >= 3 && Number.isFinite(Number(rawCd[i][2]))) {
                                rawTs = Number(rawCd[i][2]);
                            }
                        } else if (rawTxts && typeof rawTxts[i] === "string") {
                            rawLabel = rawTxts[i];
                        }
                        bestPt = {
                            cx: ptCx,
                            cy: ptCy,
                            valY: Number.isFinite(valYNum) ? valYNum : ptCy,
                            rawX: rawXs ? rawXs[i] : undefined,
                            rawLabel: rawLabel,
                            rawTs: rawTs,
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
        let fbLabel = undefined;
        let fbTs = undefined;
        const tr0 = dataArr[0];
        if (tr0 && Array.isArray(tr0.customdata) && tr0.customdata.length) {
            const idxF = Math.max(0, Math.min(tr0.customdata.length - 1, Math.round(cx)));
            const rowCd = tr0.customdata[idxF];
            if (Array.isArray(rowCd) && typeof rowCd[0] === "string") {
                fbLabel = rowCd[0];
                if (rowCd.length >= 3 && Number.isFinite(Number(rowCd[2]))) fbTs = Number(rowCd[2]);
            }
        }
        return {
            cx: cx,
            cy: cy,
            valY: Number.isFinite(valY) ? valY : cy,
            rawX: undefined,
            rawLabel: fbLabel,
            rawTs: fbTs,
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
        const temRawTs = Number.isFinite(stM.p1.rawTs) && Number.isFinite(stM.p2.rawTs);
        if (xa.type === "date" || temRawTs) {
            const msDiff = temRawTs ? Math.abs(stM.p2.rawTs - stM.p1.rawTs) : Math.abs(stM.p2.cx - stM.p1.cx);
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
