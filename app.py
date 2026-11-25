import html
import math
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone
import pandas as pd
import requests
import streamlit as st
import yfinance as yf
from bs4 import BeautifulSoup

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


def fmt_num(val: float, casas: int = 2) -> str:
    s = f"{val:,.{casas}f}"
    return s.replace(",", "X").replace(".", ",").replace("X", ".")


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
            "ticker": papel,
            "nome": papel,
            "cotacao": cotacao,
            "dy_12m": dy,
            "pl": pl,
            "pvp": pvp,
            "roe": roe,
            "lpa": lpa,
            "vpa": vpa,
            "dpa_12m": dpa_12m,
            "liq_2m": liq_2m,
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


def _fetch_yf(ticker: str) -> tuple[str, dict]:
    try:
        tk = yf.Ticker(f"{ticker}.SA")
        info = tk.info or {}

        nome_raw = info.get("shortName") or info.get("longName") or ticker
        nome = " ".join(nome_raw.split())

        lpa = info.get("trailingEps")
        vpa = info.get("bookValue")
        roe_raw = info.get("returnOnEquity")
        roe = (roe_raw * 100) if roe_raw is not None else None

        divs = tk.dividends
        dpa_12m = None
        dpa_med_6a = None
        anos_hist = 0

        if divs is not None and not divs.empty:
            divs.index = pd.to_datetime(divs.index).tz_localize(None)
            hoje = pd.Timestamp.now().tz_localize(None)

            inicio_12m = hoje - timedelta(days=365)
            dpa_12m = float(divs[divs.index >= inicio_12m].sum())

            ano_atual = hoje.year
            anos_validos = [a for a in range(ano_atual - 6, ano_atual)]
            divs_6a = divs[divs.index.year.isin(anos_validos)]
            if not divs_6a.empty:
                por_ano = divs_6a.groupby(divs_6a.index.year).sum()
                anos_hist = len(por_ano)
                divisor = min(6, max(1, anos_hist))
                dpa_med_6a = float(divs_6a.sum() / divisor)

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
        cor = "#22c55e"
        status = "🟢 (abaixo)"
    else:
        cor = "#ef4444"
        status = "🔴 (acima)"
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
    if pvp is not None and pvp > 0:
        pts_pvp = max(0.0, min(15.0, ((2.5 - pvp) / 1.5) * 15.0)) + (5.0 if pvp < 1.0 else 0.0)
    else:
        pts_pvp = 0.0

    pl = d["pl"]
    if pl is not None and pl > 0:
        pts_pl = max(0.0, min(15.0, ((20.0 - pl) / 15.0) * 15.0))
    else:
        pts_pl = 0.0

    roe = d["roe"]
    if roe is not None and roe > 0:
        pts_roe = min(20.0, (roe / 25.0) * 20.0)
    else:
        pts_roe = 0.0

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


# --- INTERFACE ---
st.title("📊 Painel Completo da B3 — Valuation & Setores")
st.caption("Todos os ativos da bolsa, filtro por Setor / BESST, ordenação por coluna, comparador e ranking de atratividade.")

try:
    with st.spinner("Carregando todos os ativos da B3..."):
        todos_ativos = carregar_todos_ativos_b3()
        setores_dict = carregar_setores_fundamentus()
except Exception as exc:
    st.error(f"Erro ao conectar com o Fundamentus: {exc}")
    st.stop()

# --- BARRA LATERAL (FILTROS) ---
with st.sidebar:
    st.header("🔍 Filtros da Bolsa")

    opcoes_filtro = [
        "Todos os Ativos da B3",
        "🌟 BESST (Bancos, Energia, Saneamento, Seguros e Telecom)",
    ] + sorted(setores_dict.keys())

    filtro_setor = st.selectbox("Filtrar por Setor:", opcoes_filtro, index=0)

    liq_min_opcoes = {
        "R$ 100 mil/dia (recomendado)": 100_000,
        "R$ 1 milhão/dia (alta liquidez)": 1_000_000,
        "R$ 0 (mostrar literalmente todas)": 0,
    }
    liq_label = st.selectbox("Liquidez mínima (2 meses):", list(liq_min_opcoes.keys()), index=0)
    liq_min = liq_min_opcoes[liq_label]

    busca_tickers = st.text_input(
        "Buscar tickers específicos (opcional):",
        placeholder="Ex: BBAS3, BBDC3, TAEE11",
        help="Se preencher aqui, filtra apenas os códigos digitados."
    )

    if st.button("🔄 Atualizar Dados", type="primary", use_container_width=True):
        st.cache_data.clear()
        st.rerun()

# Aplica filtro de setor
mapa_setores_ativos = {}
ativos_filtrados = todos_ativos

if filtro_setor == "🌟 BESST (Bancos, Energia, Saneamento, Seguros e Telecom)":
    ids_besst = tuple(setores_dict[s] for s in BESST_SETORES if s in setores_dict)
    if ids_besst:
        with st.spinner("Filtrando empresas do setor BESST..."):
            mapa_setores_ativos = carregar_tickers_por_setor(ids_besst)
        ativos_filtrados = [a for a in todos_ativos if a["ticker"] in mapa_setores_ativos]
elif filtro_setor != "Todos os Ativos da B3":
    sid = setores_dict.get(filtro_setor)
    if sid:
        with st.spinner(f"Filtrando setor {filtro_setor}..."):
            mapa_setores_ativos = carregar_tickers_por_setor((sid,))
        ativos_filtrados = [a for a in todos_ativos if a["ticker"] in mapa_setores_ativos]

# Aplica filtro de busca por ticker ou liquidez
if busca_tickers.strip():
    lista_busca = {x.strip().upper().replace(".SA", "") for x in busca_tickers.split(",") if x.strip()}
    ativos_filtrados = [a for a in ativos_filtrados if a["ticker"] in lista_busca]
else:
    ativos_filtrados = [a for a in ativos_filtrados if a["liq_2m"] >= liq_min]

if not ativos_filtrados:
    st.warning("Nenhum ativo encontrado com esses filtros. Tente reduzir a liquidez mínima.")
    st.stop()

# Cálculo preliminar rápido para definir quem já tem histórico 6a/Proj carregado automaticamente
preliminares = []
for a in ativos_filtrados:
    pt_bazin = a["dpa_12m"] / 0.06 if a["dpa_12m"] > 0 else None
    graham = math.sqrt(22.5 * a["lpa"] * a["vpa"]) if (a["lpa"] and a["vpa"] and a["lpa"] > 0 and a["vpa"] > 0) else None
    score_pre, _, _ = calcular_score(a, None, None, pt_bazin, graham)
    preliminares.append((score_pre, a))

preliminares.sort(key=lambda x: x[0], reverse=True)

# Se tiver até 55 ativos (ex: BESST ou setor individual), busca 6 anos + Projetivo de todos.
# Se tiver mais (ex: Todos da B3), busca os Top 30 automaticamente (ou todos se o usuário clicar).
carregar_todos_yf = False
if len(ativos_filtrados) > 55:
    carregar_todos_yf = st.checkbox(
        f"📥 Carregar histórico de 6 anos e Projetivo (Yahoo Finance) para TODOS os {len(ativos_filtrados)} ativos (padrão: Top 30 mais atrativos para ser instantâneo)",
        value=False,
    )

limite_yf = len(preliminares) if (len(preliminares) <= 55 or carregar_todos_yf) else 30
tickers_para_yf = tuple(item[1]["ticker"] for item in preliminares[:limite_yf])

with st.spinner(f"Buscando histórico de 6 anos e nomes na B3 para {len(tickers_para_yf)} ativos..."):
    dados_yf = buscar_yahoo_lote(tickers_para_yf)

# Consolida todos os dados
resultados = []
data_ref = datetime.now(BRT).strftime("%d/%m/%Y %H:%M")

for _, a in preliminares:
    t = a["ticker"]
    yf_info = dados_yf.get(t, {})

    nome = yf_info.get("nome") or mapa_setores_ativos.get(t) or t
    lpa = yf_info.get("lpa_yf") if yf_info.get("lpa_yf") is not None else a["lpa"]
    vpa = yf_info.get("vpa_yf") if yf_info.get("vpa_yf") is not None else a["vpa"]
    roe = a["roe"] if a["roe"] is not None else yf_info.get("roe_yf")

    dpa_12m = yf_info.get("dpa_12m_yf") if yf_info.get("dpa_12m_yf") is not None else a["dpa_12m"]
    dy_12m = (dpa_12m / a["cotacao"]) * 100 if (dpa_12m and a["cotacao"] > 0) else a["dy_12m"]
    dpa_med_6a = yf_info.get("dpa_med_6a")
    anos_hist = yf_info.get("anos_hist", 0)
    dpa_proj = yf_info.get("dpa_proj")

    pt_med = (dpa_med_6a / 0.06) if (dpa_med_6a and dpa_med_6a > 0) else None
    pt_proj = (dpa_proj / 0.06) if (dpa_proj and dpa_proj > 0) else None
    pt_bazin = (dpa_12m / 0.06) if (dpa_12m and dpa_12m > 0) else None
    graham = math.sqrt(22.5 * lpa * vpa) if (lpa and vpa and lpa > 0 and vpa > 0) else None

    item_calc = {
        **a,
        "nome": nome,
        "setor_nome": mapa_setores_ativos.get(t, ""),
        "lpa": lpa,
        "vpa": vpa,
        "roe": roe,
        "dpa_12m": dpa_12m,
        "dy_12m": dy_12m,
        "dpa_med_6a": dpa_med_6a,
        "anos_hist": anos_hist,
        "dpa_proj": dpa_proj,
        "pt_med": pt_med,
        "pt_proj": pt_proj,
        "pt_bazin": pt_bazin,
        "graham": graham,
    }

    score, avg_ms, motivos = calcular_score(item_calc, pt_med, pt_proj, pt_bazin, graham)
    item_calc["score"] = score
    item_calc["avg_ms"] = avg_ms
    item_calc["motivos"] = motivos
    resultados.append(item_calc)

# Define posição oficial no Ranking de Atratividade (antes da ordenação personalizada por coluna)
resultados.sort(key=lambda x: x["score"], reverse=True)
for idx, r in enumerate(resultados, start=1):
    r["pos_ranking"] = idx

tab1, tab2 = st.tabs([f"📊 Tabela & Ranking ({len(resultados)} ativos)", "⚖️ Comparar Ativos"])

with tab1:
    # Controles de ordenação por coluna
    col_ord1, col_ord2, col_ord3 = st.columns([2, 1.5, 1.5])
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
    with col_ord1:
        col_escolhida = st.selectbox("Ordenar tabela por coluna:", list(opcoes_ordenacao.keys()), index=0)
    with col_ord2:
        dir_padrao = 1 if col_escolhida in ("P/L", "P/VP", "Ticker (A-Z)") else 0
        direcao = st.selectbox("Ordem:", ["Decrescente (Maior → Menor)", "Crescente (Menor → Maior)"], index=dir_padrao)
    with col_ord3:
        max_linhas = st.selectbox("Exibir na tabela:", [30, 50, 100, "Todos"], index=1 if len(resultados) > 50 else 3)

    chave_ord = opcoes_ordenacao[col_escolhida]
    reverso = direcao.startswith("Decrescente")
    resultados_ordenados = sort_resultados(resultados, chave_ord, reverso)
    exibir = resultados_ordenados if max_linhas == "Todos" else resultados_ordenados[:int(max_linhas)]

    linhas_html = []
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

        linhas_html.append(f"""
        <tr>
            <td style="text-align:center; font-weight:700;">{r['pos_ranking']}º<br><small style="opacity:0.75;">{r['score']}</small></td>
            <td><strong>{r['ticker']}</strong><br><small style="opacity:0.8;">{nome_esc}</small>{setor_badge}</td>
            <td><strong>R$ {fmt_num(cot)}</strong><br><small>DY: {fmt_num(r['dy_12m'])}%</small></td>
            <td>P/L: {pl_txt}<br>P/VP: {pvp_html}<br>ROE: {roe_txt}</td>
            <td>LPA: {lpa_txt} | VPA: {vpa_txt}<br>12m: R$ {fmt_num(r['dpa_12m'])} | 6a: {dpa6_txt}<br>Proj: {dpap_txt}</td>
            <td>{html_preco_ms(r['pt_med'], cot, sufixo_6a)}</td>
            <td>{html_preco_ms(r['pt_proj'], cot)}</td>
            <td>{html_preco_ms(r['pt_bazin'], cot)}</td>
            <td>{html_preco_ms(r['graham'], cot)}</td>
        </tr>
        """)

    tabela_html = f"""
    <style>
        .val-table-wrap {{ width: 100%; overflow-x: auto; }}
        .val-table {{
            width: 100%;
            border-collapse: collapse;
            font-size: 13px;
            line-height: 1.4;
        }}
        .val-table th {{
            background-color: rgba(128, 128, 128, 0.18);
            text-align: left;
            padding: 8px 6px;
            border-bottom: 2px solid rgba(128, 128, 128, 0.35);
            font-weight: 600;
            font-size: 12px;
        }}
        .val-table td {{
            padding: 8px 6px;
            border-bottom: 1px solid rgba(128, 128, 128, 0.22);
            vertical-align: middle;
        }}
        .val-table tr:hover td {{
            background-color: rgba(128, 128, 128, 0.08);
        }}
    </style>
    <div class="val-table-wrap">
        <table class="val-table">
            <thead>
                <tr>
                    <th style="text-align:center;">Rank<br><small>Score</small></th>
                    <th>Ticker / Empresa</th>
                    <th>Cotação ({data_ref}) & DY</th>
                    <th>Indicadores<br><small>(P/L | P/VP | ROE)</small></th>
                    <th>Dados Base<br><small>(LPA | VPA | DPAs)</small></th>
                    <th>Preço Teto Médio (6a) & MS</th>
                    <th>Preço Teto Projetivo & MS</th>
                    <th>Preço-Teto Bazin (12m) & MS</th>
                    <th>Preço Justo Graham & MS</th>
                </tr>
            </thead>
            <tbody>
                {"".join(linhas_html)}
            </tbody>
        </table>
    </div>
    """
    st.markdown(tabela_html, unsafe_allow_html=True)

    # Legenda compacta das siglas e nota do asterisco
    st.caption(
        "**Legenda siglas B3:** `ON` = Ordinária (voto) · `PN` = Preferencial (dividendos) · `UNT` = Unit (ON+PN) · "
        "`ED/EJ` = Ex-Dividendo/JCP · `N1/N2/NM` = Nível 1, Nível 2 e Novo Mercado (governança).  \n"
        "(*) Ativos com asterisco possuem menos de 6 anos completos de proventos no Yahoo Finance."
    )

    st.subheader("🏆 Top 10 do Ranking de Atratividade (Filtro Atual)")
    for r in resultados[:10]:
        justificativa = "; ".join(r["motivos"]).capitalize() + "." if r["motivos"] else "Sem dados suficientes."
        st.markdown(
            f"**{r['pos_ranking']}º Lugar: {r['ticker']}** ({r['nome']}) | "
            f"**Cotação: R$ {fmt_num(r['cotacao'])}** | "
            f"**Score: {r['score']}/100**  \n"
            f"_{justificativa}_"
        )

with tab2:
    st.subheader("⚖️ Comparador Lado a Lado")
    opcoes_comp = [r["ticker"] for r in resultados]
    selecionados = st.multiselect(
        "Escolha 2 ou mais ativos do filtro atual para comparar:",
        options=opcoes_comp,
        default=opcoes_comp[:min(3, len(opcoes_comp))],
    )

    if len(selecionados) < 2:
        st.info("Selecione pelo menos 2 ativos acima para visualizar a comparação.")
    else:
        # Garante dados completos do Yahoo Finance caso algum escolhido não estivesse no Top 30
        faltantes = tuple(t for t in selecionados if t not in dados_yf)
        extra_yf = buscar_yahoo_lote(faltantes) if faltantes else {}

        itens_comp = []
        for r in resultados:
            if r["ticker"] in selecionados:
                if r["ticker"] in extra_yf and extra_yf[r["ticker"]]:
                    yf_i = extra_yf[r["ticker"]]
                    r = dict(r)
                    r["nome"] = yf_i.get("nome") or r["nome"]
                    r["dpa_med_6a"] = yf_i.get("dpa_med_6a")
                    r["dpa_proj"] = yf_i.get("dpa_proj")
                    r["pt_med"] = (r["dpa_med_6a"] / 0.06) if (r["dpa_med_6a"] and r["dpa_med_6a"] > 0) else None
                    r["pt_proj"] = (r["dpa_proj"] / 0.06) if (r["dpa_proj"] and r["dpa_proj"] > 0) else None
                itens_comp.append(r)

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

        st.markdown("### 🏆 Destaques entre os selecionados")
        v_score = max(itens_comp, key=lambda x: x["score"])
        v_dy = max(itens_comp, key=lambda x: x["dy_12m"])
        pl_pos = [x for x in itens_comp if x["pl"] and x["pl"] > 0]
        pvp_pos = [x for x in itens_comp if x["pvp"] and x["pvp"] > 0]
        roe_pos = [x for x in itens_comp if x["roe"] is not None]
        ms_pos = [x for x in itens_comp if x["avg_ms"] is not None]

        c1, c2, c3 = st.columns(3)
        c1.success(f"**Melhor Score:** {v_score['ticker']} ({v_score['score']}/100)")
        if ms_pos:
            v_ms = max(ms_pos, key=lambda x: x["avg_ms"])
            c2.success(f"**Maior Margem Média:** {v_ms['ticker']} ({v_ms['avg_ms']:+.1f}%)")
        c3.success(f"**Maior DY 12m:** {v_dy['ticker']} ({fmt_num(v_dy['dy_12m'])}%)")

        c4, c5, c6 = st.columns(3)
        if pl_pos:
            v_pl = min(pl_pos, key=lambda x: x["pl"])
            c4.info(f"**Menor P/L:** {v_pl['ticker']} ({fmt_num(v_pl['pl'])})")
        if pvp_pos:
            v_pvp = min(pvp_pos, key=lambda x: x["pvp"])
            c5.info(f"**Menor P/VP:** {v_pvp['ticker']} ({fmt_num(v_pvp['pvp'])})")
        if roe_pos:
            v_roe = max(roe_pos, key=lambda x: x["roe"])
            c6.info(f"**Maior ROE:** {v_roe['ticker']} ({fmt_num(v_roe['roe'], 1)}%)")

st.divider()
st.caption("Aviso: Estudo quantitativo e educacional com dados obtidos via Fundamentus e Yahoo Finance. Não constitui recomendação oficial de compra ou venda.")
