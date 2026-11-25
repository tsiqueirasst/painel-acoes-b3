import html
import io
import math
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone
from urllib.parse import urlencode
import pandas as pd
import plotly.graph_objects as go
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


def parse_carteira_str(raw: str) -> list[dict]:
    itens = []
    if not raw:
        return itens
    for bloco in raw.split(";"):
        partes = bloco.split(":")
        if len(partes) == 3:
            t = partes[0].strip().upper().replace(".SA", "")
            try:
                qtd = float(partes[1])
                pm = float(partes[2])
                if t and qtd > 0 and pm >= 0:
                    itens.append({"ticker": t, "qtd": qtd, "pm": pm})
            except ValueError:
                continue
    return itens


def serializar_carteira(lista: list[dict]) -> str:
    return ";".join(f"{x['ticker']}:{x['qtd']:g}:{x['pm']:.2f}" for x in lista)


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
            ultimo_dia = df.index.date[-1]
            df = df[df.index.date == ultimo_dia]
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
def buscar_historico_fundamentalista(ticker: str) -> list[dict]:
    tk = yf.Ticker(f"{ticker}.SA")
    info = tk.info or {}
    fin = tk.financials
    bal = tk.balance_sheet
    qfin = tk.quarterly_financials
    qbal = tk.quarterly_balance_sheet

    hist_px = tk.history(period="6y", interval="1d", auto_adjust=False)
    if not hist_px.empty:
        hist_px.index = pd.to_datetime(hist_px.index).tz_localize(None)

    acoes_info = info.get("sharesOutstanding")
    cot_atual = info.get("currentPrice") or info.get("regularMarketPrice")
    if not cot_atual and not hist_px.empty:
        cot_atual = float(hist_px["Close"].iloc[-1])

    linhas = []

    # Colunas anuais disponíveis (ordenadas do ano mais antigo ao mais recente)
    if fin is not None and not fin.empty:
        cols_fin = sorted(list(fin.columns), key=lambda c: pd.to_datetime(c))
        cols_bal = list(bal.columns) if (bal is not None and not bal.empty) else []

        for col_f in cols_fin[-5:]:
            ano = pd.to_datetime(col_f).year
            # Encontra coluna do balanço do mesmo ano
            col_b = next((cb for cb in cols_bal if pd.to_datetime(cb).year == ano), None)

            rec = _pick_row(fin, ["Total Revenue", "Operating Revenue"], col_f)
            lbr = _pick_row(fin, ["Gross Profit"], col_f)
            lliq = _pick_row(fin, ["Net Income", "Net Income Common Stockholders"], col_f)
            ebitda = _pick_row(fin, ["EBITDA", "Normalized EBITDA"], col_f)
            if ebitda is None:
                ebit = _pick_row(fin, ["Operating Income", "EBIT"], col_f)
                dep = _pick_row(fin, ["Reconciled Depreciation", "Depreciation And Amortization"], col_f)
                if ebit is not None and dep is not None:
                    ebitda = ebit + dep

            patr = _pick_row(bal, ["Stockholders Equity", "Total Equity Gross Minority Interest", "Common Stock Equity"], col_b) if col_b is not None else None
            div_liq = _pick_row(bal, ["Net Debt"], col_b) if col_b is not None else None
            if div_liq is None and col_b is not None:
                div_tot = _pick_row(bal, ["Total Debt"], col_b)
                caixa = _pick_row(bal, ["Cash And Cash Equivalents", "Cash Cash Equivalents And Short Term Investments"], col_b)
                if div_tot is not None and caixa is not None:
                    div_liq = div_tot - caixa

            acoes = _pick_row(bal, ["Ordinary Shares Number", "Share Issued"], col_b) if col_b is not None else None
            if not acoes:
                acoes = acoes_info

            px_ano = None
            if not hist_px.empty:
                sub = hist_px[hist_px.index.year == ano]
                if not sub.empty:
                    px_ano = float(sub["Close"].iloc[-1])

            vpa = (patr / acoes) if (patr and acoes and acoes > 0) else None
            val_merc = (px_ano * acoes) if (px_ano and acoes and acoes > 0) else None
            pl = (val_merc / lliq) if (val_merc and lliq and lliq != 0) else None
            pvp = (val_merc / patr) if (val_merc and patr and patr != 0) else None
            pebitda = (val_merc / ebitda) if (val_merc and ebitda and ebitda != 0) else None
            marg_liq = (lliq / rec * 100) if (lliq is not None and rec and rec != 0) else None

            linhas.append({
                "ano": str(ano),
                "pl": pl, "pvp": pvp, "vpa": vpa, "div_liq": div_liq,
                "marg_liq": marg_liq, "ebitda": ebitda, "pebitda": pebitda,
                "val_merc": val_merc, "lliq": lliq, "lbr": lbr, "rec": rec,
            })

    # Linha ÚLT. 12M (soma últimos 4 trimestres + último balanço)
    if qfin is not None and not qfin.empty:
        qcols = sorted(list(qfin.columns), key=lambda c: pd.to_datetime(c), reverse=True)[:4]
        if len(qcols) >= 4:
            def _sum_q(cands):
                vals = [_pick_row(qfin, cands, c) for c in qcols]
                valid = [v for v in vals if v is not None]
                return sum(valid) if len(valid) == 4 else None

            rec_12 = _sum_q(["Total Revenue", "Operating Revenue"])
            lbr_12 = _sum_q(["Gross Profit"])
            lliq_12 = _sum_q(["Net Income", "Net Income Common Stockholders"])
            ebitda_12 = _sum_q(["EBITDA", "Normalized EBITDA"])

            col_qb = sorted(list(qbal.columns), key=lambda c: pd.to_datetime(c), reverse=True)[0] if (qbal is not None and not qbal.empty) else None
            patr_12 = _pick_row(qbal, ["Stockholders Equity", "Total Equity Gross Minority Interest", "Common Stock Equity"], col_qb) if col_qb is not None else None
            div_liq_12 = _pick_row(qbal, ["Net Debt"], col_qb) if col_qb is not None else None
            if div_liq_12 is None and col_qb is not None:
                dt12 = _pick_row(qbal, ["Total Debt"], col_qb)
                cx12 = _pick_row(qbal, ["Cash And Cash Equivalents", "Cash Cash Equivalents And Short Term Investments"], col_qb)
                if dt12 is not None and cx12 is not None:
                    div_liq_12 = dt12 - cx12
            acoes_12 = (_pick_row(qbal, ["Ordinary Shares Number", "Share Issued"], col_qb) if col_qb is not None else None) or acoes_info

            vpa_12 = (patr_12 / acoes_12) if (patr_12 and acoes_12 and acoes_12 > 0) else info.get("bookValue")
            val_merc_12 = info.get("marketCap") or ((cot_atual * acoes_12) if (cot_atual and acoes_12) else None)
            pl_12 = (val_merc_12 / lliq_12) if (val_merc_12 and lliq_12 and lliq_12 != 0) else info.get("trailingPE")
            pvp_12 = (val_merc_12 / patr_12) if (val_merc_12 and patr_12 and patr_12 != 0) else info.get("priceToBook")
            pebitda_12 = (val_merc_12 / ebitda_12) if (val_merc_12 and ebitda_12 and ebitda_12 != 0) else None
            marg_12 = (lliq_12 / rec_12 * 100) if (lliq_12 is not None and rec_12 and rec_12 != 0) else None

            linhas.append({
                "ano": "ÚLT. 12M",
                "pl": pl_12, "pvp": pvp_12, "vpa": vpa_12, "div_liq": div_liq_12,
                "marg_liq": marg_12, "ebitda": ebitda_12, "pebitda": pebitda_12,
                "val_merc": val_merc_12, "lliq": lliq_12, "lbr": lbr_12, "rec": rec_12,
            })

    return linhas


def render_grafico_e_tabela_ativo(ticker: str, nome: str = "", key_prefix: str = "raiox"):
    st.markdown(f"### 📈 COTAÇÃO {ticker} {f'— {nome}' if nome and nome != ticker else ''}")

    c_per, c_tipo = st.columns([3, 1.2])
    with c_per:
        periodo = st.radio(
            "Período:",
            ["1 D", "7 D", "30 D", "6 M", "YTD", "1 A", "5 A", "10 A", "15 A"],
            index=5,
            horizontal=True,
            key=f"{key_prefix}_per_{ticker}",
        )
    with c_tipo:
        tipo_cot = st.selectbox(
            "Tipo:",
            ["Cotação ajustada", "Cotação simples"],
            index=0,
            key=f"{key_prefix}_tipo_{ticker}",
        )

    ajustada = tipo_cot == "Cotação ajustada"
    serie = buscar_historico_preco(ticker, periodo, ajustada)

    if serie.empty:
        st.warning(f"Não foi possível carregar o gráfico de {ticker} para o período {periodo}.")
    else:
        p_ini = float(serie.iloc[0])
        p_fim = float(serie.iloc[-1])
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
                x=serie.index,
                y=serie.values,
                mode="lines",
                line=dict(color=cor, width=2.2),
                fill="tozeroy",
                fillcolor=fill_cor,
                hovertemplate=f"{fmt_hover}<br><b>R$ %{{y:.2f}}</b><extra></extra>",
            )
        )
        y_min = float(serie.min())
        y_max = float(serie.max())
        margem_y = (y_max - y_min) * 0.08 if y_max > y_min else y_max * 0.05

        fig.update_layout(
            height=330,
            margin=dict(l=10, r=65, t=15, b=15),
            paper_bgcolor="rgba(0,0,0,0)",
            plot_bgcolor="rgba(0,0,0,0)",
            showlegend=False,
            hovermode="x unified",
            xaxis=dict(showgrid=False, zeroline=False),
            yaxis=dict(
                showgrid=True,
                gridcolor="rgba(128,128,128,0.25)",
                tickprefix="R$ ",
                range=[max(0, y_min - margem_y), y_max + margem_y],
            ),
            annotations=[
                dict(
                    xref="paper", x=1.01, y=p_fim, xanchor="left", yanchor="middle",
                    text=f"<b>{fmt_num(p_fim)}</b>",
                    showarrow=False,
                    font=dict(color="white", size=12),
                    bgcolor=cor, borderpad=4,
                )
            ],
        )
        st.plotly_chart(fig, use_container_width=True, key=f"{key_prefix}_plot_{ticker}")

        # Simulador "Se você tivesse investido..."
        serie_max = buscar_serie_max_ajustada(ticker)
        if not serie_max.empty:
            s1, s2, s3 = st.columns([1.4, 1.2, 2.2])
            with s1:
                valor_inv = st.number_input(
                    "Se você tivesse investido (R$):",
                    min_value=10.0, value=1000.0, step=100.0,
                    key=f"{key_prefix}_val_{ticker}",
                )
            with s2:
                janela_sim = st.selectbox(
                    "Há:",
                    ["1 mês", "6 meses", "1 ano", "5 anos", "10 anos", "15 anos"],
                    index=2,
                    key=f"{key_prefix}_jan_{ticker}",
                )
            deltas = {
                "1 mês": pd.DateOffset(months=1),
                "6 meses": pd.DateOffset(months=6),
                "1 ano": pd.DateOffset(years=1),
                "5 anos": pd.DateOffset(years=5),
                "10 anos": pd.DateOffset(years=10),
                "15 anos": pd.DateOffset(years=15),
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

    # Tabela Histórica estilo Imagem 2
    st.markdown(f"#### 📑 Histórico Fundamentalista — {ticker}")
    hist_fund = buscar_historico_fundamentalista(ticker)
    if not hist_fund:
        st.info("Histórico anual detalhado indisponível para este ativo no Yahoo Finance.")
    else:
        rows_h = []
        for h in hist_fund:
            pl_s = fmt_num(h["pl"]) if h["pl"] is not None else "—"
            pvp_s = fmt_num(h["pvp"]) if h["pvp"] is not None else "—"
            vpa_s = fmt_num(h["vpa"]) if h["vpa"] is not None else "—"
            ml_s = f"{fmt_num(h['marg_liq'])}%" if h["marg_liq"] is not None else "—"
            peb_s = fmt_num(h["pebitda"]) if h["pebitda"] is not None else "—"
            rows_h.append(
                "<tr>"
                f"<td style='font-weight:700;'>{h['ano']}</td>"
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


# --- ESTADO INICIAL DA CARTEIRA ---
if "carteira" not in st.session_state:
    st.session_state["carteira"] = parse_carteira_str(st.query_params.get("carteira", ""))

# --- INTERFACE PRINCIPAL ---
st.title("📊 Painel Completo da B3 — Valuation, Raio-X & Carteira")
st.caption("Todos os ativos da bolsa, Setor BESST, gráfico histórico interativo, balanço anual e gestão da sua carteira.")

try:
    with st.spinner("Carregando todos os ativos da B3..."):
        todos_ativos = carregar_todos_ativos_b3()
        setores_dict = carregar_setores_fundamentus()
except Exception as exc:
    st.error(f"Erro ao conectar com o Fundamentus: {exc}")
    st.stop()

# --- BARRA LATERAL ---
with st.sidebar:
    st.header("🔍 Filtros da Bolsa")

    opcoes_filtro = [
        "Todos os Ativos da B3",
        "🌟 BESST (Bancos, Energia, Saneamento, Seguros e Telecom)",
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
        "Buscar tickers específicos (opcional):",
        value=st.query_params.get("busca", ""),
        placeholder="Ex: BBAS3, BBDC3, TAEE11",
    )

    if st.button("🔄 Atualizar Dados", type="primary", use_container_width=True):
        st.cache_data.clear()
        st.rerun()

# Sincroniza query params com filtros atuais
st.query_params["setor"] = filtro_setor
st.query_params["liq"] = liq_label
if busca_tickers.strip():
    st.query_params["busca"] = busca_tickers.strip()
elif "busca" in st.query_params:
    del st.query_params["busca"]
carteira_str = serializar_carteira(st.session_state["carteira"])
if carteira_str:
    st.query_params["carteira"] = carteira_str
elif "carteira" in st.query_params:
    del st.query_params["carteira"]

# Aplica filtros
mapa_setores_ativos = {}
ativos_filtrados = todos_ativos

if filtro_setor == "🌟 BESST (Bancos, Energia, Saneamento, Seguros e Telecom)":
    ids_besst = tuple(setores_dict[s] for s in BESST_SETORES if s in setores_dict)
    if ids_besst:
        with st.spinner("Filtrando empresas do setor BESST..."):
            mapa_setores_ativos = carregar_tickers_por_setor(ids_besst)
        ativos_filtrados = [a for a in todos_ativos if a["ticker"] in mapa_setores_ativos]
elif filtro_setor == "💼 Apenas Minha Carteira":
    tickers_cart = {x["ticker"] for x in st.session_state["carteira"]}
    ativos_filtrados = [a for a in todos_ativos if a["ticker"] in tickers_cart]
elif filtro_setor != "Todos os Ativos da B3":
    sid = setores_dict.get(filtro_setor)
    if sid:
        with st.spinner(f"Filtrando setor {filtro_setor}..."):
            mapa_setores_ativos = carregar_tickers_por_setor((sid,))
        ativos_filtrados = [a for a in todos_ativos if a["ticker"] in mapa_setores_ativos]

if busca_tickers.strip():
    lista_busca = {x.strip().upper().replace(".SA", "") for x in busca_tickers.split(",") if x.strip()}
    ativos_filtrados = [a for a in ativos_filtrados if a["ticker"] in lista_busca]
elif filtro_setor != "💼 Apenas Minha Carteira":
    ativos_filtrados = [a for a in ativos_filtrados if a["liq_2m"] >= liq_min]

# Preliminar para definir quais buscam Yahoo Finance
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
# Garante também carregar os ativos da carteira e o ativo clicado
ativo_url = st.query_params.get("ativo", "").strip().upper()
extras_obrigatorios = [x["ticker"] for x in st.session_state["carteira"]] + ([ativo_url] if ativo_url else [])
for ex in extras_obrigatorios:
    if ex and ex not in tickers_para_yf:
        tickers_para_yf.append(ex)

with st.spinner(f"Buscando dados de 6 anos e nomes na B3 para {len(tickers_para_yf)} ativos..."):
    dados_yf = buscar_yahoo_lote(tuple(tickers_para_yf))

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
        "lpa": lpa, "vpa": vpa, "roe": roe,
        "dpa_12m": dpa_12m, "dy_12m": dy_12m,
        "dpa_med_6a": dpa_med_6a, "anos_hist": anos_hist, "dpa_proj": dpa_proj,
        "pt_med": pt_med, "pt_proj": pt_proj, "pt_bazin": pt_bazin, "graham": graham,
    }
    score, avg_ms, motivos = calcular_score(item_calc, pt_med, pt_proj, pt_bazin, graham)
    item_calc["score"] = score
    item_calc["avg_ms"] = avg_ms
    item_calc["motivos"] = motivos
    resultados.append(item_calc)

resultados.sort(key=lambda x: x["score"], reverse=True)
for idx, r in enumerate(resultados, start=1):
    r["pos_ranking"] = idx

tab1, tab2, tab3 = st.tabs([
    f"📊 Tabela & Raio-X ({len(resultados)} ativos)",
    "⚖️ Comparar Ativos",
    f"💼 Minha Carteira ({len(st.session_state['carteira'])})",
])

# ==================== ABA 1: TABELA, RAIO-X E RANKING ====================
with tab1:
    if not resultados:
        st.info("Nenhum ativo encontrado no filtro atual. Se selecionou 'Apenas Minha Carteira', cadastre seus ativos na aba 💼 Minha Carteira.")
    else:
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

        with st.expander(f"📋 Tabela Comparativa ({len(exibir)} ativos exibidos) — clique para minimizar/maximizar | clique em um Ticker para abrir o Raio-X", expanded=True):
            linhas_html = []
            base_params = {"setor": filtro_setor, "liq": liq_label}
            if busca_tickers.strip():
                base_params["busca"] = busca_tickers.strip()
            if carteira_str:
                base_params["carteira"] = carteira_str

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

                params_link = {**base_params, "ativo": r["ticker"]}
                href = f"?{urlencode(params_link)}#raiox"

                linha = (
                    "<tr>"
                    f"<td style='text-align:center; font-weight:700;'>{r['pos_ranking']}º<br><small style='opacity:0.75;'>{r['score']}</small></td>"
                    f"<td><a href='{href}' target='_self' style='color:#60a5fa; text-decoration:none; font-weight:700;'>🔎 {r['ticker']}</a><br><small style='opacity:0.8;'>{nome_esc}</small>{setor_badge}</td>"
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
                f"<th>Cotação ({data_ref}) & DY</th>"
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

        # --- RAIO-X DO ATIVO SELECIONADO ---
        st.markdown("<div id='raiox'></div>", unsafe_allow_html=True)
        opcoes_raiox = [r["ticker"] for r in resultados]
        idx_raiox = opcoes_raiox.index(ativo_url) if ativo_url in opcoes_raiox else 0
        with st.container(border=True):
            ativo_escolhido = st.selectbox(
                "🔎 Raio-X do Ativo (ou clique diretamente no código azul da tabela acima):",
                options=opcoes_raiox,
                index=idx_raiox,
            )
            item_raiox = next(r for r in resultados if r["ticker"] == ativo_escolhido)
            render_grafico_e_tabela_ativo(ativo_escolhido, item_raiox["nome"], key_prefix="tab1")

        # --- TOP 100 RANKING ---
        qtd_top = min(100, len(resultados))
        st.subheader(f"🏆 Top {qtd_top} do Ranking de Atratividade (Filtro Atual)")
        blocos_ranking = []
        for r in resultados[:100]:
            justificativa = "; ".join(r["motivos"]).capitalize() + "." if r["motivos"] else "Sem dados suficientes."
            blocos_ranking.append(
                f"**{r['pos_ranking']}º Lugar: {r['ticker']}** ({r['nome']}) | "
                f"**Cotação: R$ {fmt_num(r['cotacao'])}** | "
                f"**Score: {r['score']}/100**  \n"
                f"_{justificativa}_"
            )
        st.markdown("\n\n".join(blocos_ranking))

# ==================== ABA 2: COMPARAR ATIVOS ====================
with tab2:
    st.subheader("⚖️ Comparador Lado a Lado")
    opcoes_comp = [a["ticker"] for a in todos_ativos]
    default_comp = [r["ticker"] for r in resultados[:min(3, len(resultados))]] if resultados else opcoes_comp[:3]
    selecionados = st.multiselect(
        "Escolha 2 ou mais ativos para comparar:",
        options=opcoes_comp,
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
                base = mapa_todos[t]
                yf_i = dados_yf.get(t) or extra_yf.get(t, {})
                nome = yf_i.get("nome") or t
                lpa = yf_i.get("lpa_yf") if yf_i.get("lpa_yf") is not None else base["lpa"]
                vpa = yf_i.get("vpa_yf") if yf_i.get("vpa_yf") is not None else base["vpa"]
                roe = base["roe"] if base["roe"] is not None else yf_i.get("roe_yf")
                dpa_12m = yf_i.get("dpa_12m_yf") if yf_i.get("dpa_12m_yf") is not None else base["dpa_12m"]
                dy_12m = (dpa_12m / base["cotacao"]) * 100 if (dpa_12m and base["cotacao"] > 0) else base["dy_12m"]
                dpa_6a = yf_i.get("dpa_med_6a")
                dpa_p = yf_i.get("dpa_proj")
                pt_m = (dpa_6a / 0.06) if (dpa_6a and dpa_6a > 0) else None
                pt_p = (dpa_p / 0.06) if (dpa_p and dpa_p > 0) else None
                pt_b = (dpa_12m / 0.06) if (dpa_12m and dpa_12m > 0) else None
                gr = math.sqrt(22.5 * lpa * vpa) if (lpa and vpa and lpa > 0 and vpa > 0) else None
                tmp = {**base, "nome": nome, "lpa": lpa, "vpa": vpa, "roe": roe, "dpa_12m": dpa_12m, "dy_12m": dy_12m, "pt_med": pt_m, "pt_proj": pt_p, "pt_bazin": pt_b, "graham": gr}
                sc, ams, mot = calcular_score(tmp, pt_m, pt_p, pt_b, gr)
                tmp.update({"score": sc, "avg_ms": ams, "motivos": mot, "pos_ranking": mapa_res.get(t, {}).get("pos_ranking", "-")})
                itens_comp.append(tmp)

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

        # Gráfico comparativo de rentabilidade (%)
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

        # Raio-X individual (Imagem 1 + Imagem 2) de cada ativo comparado
        st.markdown("### 🔍 Gráfico Individual e Histórico Fundamentalista dos Ativos Comparados")
        subtabs = st.tabs([f"📊 {r['ticker']}" for r in itens_comp])
        for st_tab, r in zip(subtabs, itens_comp):
            with st_tab:
                render_grafico_e_tabela_ativo(r["ticker"], r["nome"], key_prefix="comp_sub")

# ==================== ABA 3: MINHA CARTEIRA ====================
with tab3:
    st.subheader("💼 Cadastro e Acompanhamento da Minha Carteira")
    st.caption("Cadastre seus ativos abaixo. O link do navegador é atualizado automaticamente para você salvar nos Favoritos, ou você pode exportar/importar um arquivo CSV.")

    tickers_b3 = sorted([a["ticker"] for a in todos_ativos])
    with st.form("form_add_carteira", clear_on_submit=False):
        fc1, fc2, fc3, fc4 = st.columns([1.6, 1.2, 1.2, 1])
        with fc1:
            tk_add = st.selectbox("Ativo (Ticker):", options=tickers_b3, index=tickers_b3.index("BBAS3") if "BBAS3" in tickers_b3 else 0)
        with fc2:
            qtd_add = st.number_input("Quantidade:", min_value=1.0, value=100.0, step=10.0)
        with fc3:
            pm_add = st.number_input("Preço Médio (R$):", min_value=0.01, value=15.00, step=0.50, format="%.2f")
        with fc4:
            st.markdown("<div style='padding-top:28px;'></div>", unsafe_allow_html=True)
            enviar = st.form_submit_button("➕ Salvar Ativo", type="primary", use_container_width=True)

        if enviar:
            nova = [x for x in st.session_state["carteira"] if x["ticker"] != tk_add]
            nova.append({"ticker": tk_add, "qtd": float(qtd_add), "pm": float(pm_add)})
            st.session_state["carteira"] = nova
            st.query_params["carteira"] = serializar_carteira(nova)
            st.rerun()

    # Remover ou Importar/Exportar
    c_rem, c_exp, c_imp = st.columns([2, 1.5, 2])
    with c_rem:
        if st.session_state["carteira"]:
            tk_rem = st.selectbox("Remover ativo da carteira:", ["—"] + [x["ticker"] for x in st.session_state["carteira"]])
            if tk_rem != "—" and st.button("🗑️ Remover selecionado"):
                st.session_state["carteira"] = [x for x in st.session_state["carteira"] if x["ticker"] != tk_rem]
                nv_str = serializar_carteira(st.session_state["carteira"])
                if nv_str:
                    st.query_params["carteira"] = nv_str
                elif "carteira" in st.query_params:
                    del st.query_params["carteira"]
                st.rerun()
    with c_exp:
        if st.session_state["carteira"]:
            df_exp = pd.DataFrame(st.session_state["carteira"])
            st.download_button(
                "📥 Baixar Backup (CSV)",
                data=df_exp.to_csv(index=False).encode("utf-8"),
                file_name="minha_carteira_b3.csv",
                mime="text/csv",
                use_container_width=True,
            )
    with c_imp:
        arq = st.file_uploader("📤 Importar Backup (CSV):", type=["csv"], label_visibility="collapsed")
        if arq is not None:
            try:
                df_imp = pd.read_csv(io.BytesIO(arq.getvalue()))
                if {"ticker", "qtd", "pm"}.issubset(df_imp.columns):
                    lista_imp = []
                    for _, row in df_imp.iterrows():
                        t = str(row["ticker"]).strip().upper().replace(".SA", "")
                        if t:
                            lista_imp.append({"ticker": t, "qtd": float(row["qtd"]), "pm": float(row["pm"])})
                    st.session_state["carteira"] = lista_imp
                    st.query_params["carteira"] = serializar_carteira(lista_imp)
                    st.success("Carteira importada com sucesso!")
                    st.rerun()
            except Exception as exc:
                st.error(f"Arquivo inválido: {exc}")

    if not st.session_state["carteira"]:
        st.info("Sua carteira ainda está vazia. Use o formulário acima para cadastrar seu primeiro ativo!")
    else:
        mapa_todos = {a["ticker"]: a for a in todos_ativos}
        tk_cart_tuple = tuple(x["ticker"] for x in st.session_state["carteira"] if x["ticker"] not in dados_yf)
        yf_cart = buscar_yahoo_lote(tk_cart_tuple) if tk_cart_tuple else {}

        total_investido = 0.0
        total_atual = 0.0
        renda_12m_est = 0.0
        renda_proj_est = 0.0
        linhas_cart = []

        for item in st.session_state["carteira"]:
            t = item["ticker"]
            base = mapa_todos.get(t)
            if not base:
                continue
            yf_i = dados_yf.get(t) or yf_cart.get(t, {})
            cot = base["cotacao"]
            qtd = item["qtd"]
            pm = item["pm"]
            inv = qtd * pm
            atu = qtd * cot
            lucro_rs = atu - inv
            lucro_pct = ((cot / pm) - 1) * 100 if pm > 0 else 0.0

            dpa_12m = yf_i.get("dpa_12m_yf") if yf_i.get("dpa_12m_yf") is not None else base["dpa_12m"]
            dpa_proj = yf_i.get("dpa_proj") if yf_i.get("dpa_proj") is not None else dpa_12m
            yoc = (dpa_12m / pm) * 100 if pm > 0 else 0.0

            total_investido += inv
            total_atual += atu
            renda_12m_est += qtd * dpa_12m
            renda_proj_est += qtd * dpa_proj

            linhas_cart.append({
                "Ticker": t,
                "Qtd": int(qtd) if qtd.is_integer() else qtd,
                "Preço Médio": f"R$ {fmt_num(pm)}",
                "Cotação Atual": f"R$ {fmt_num(cot)}",
                "Total Investido": f"R$ {fmt_num(inv)}",
                "Saldo Atual": f"R$ {fmt_num(atu)}",
                "Valor_Num": atu,
                "Resultado": f"R$ {fmt_num(lucro_rs)} ({lucro_pct:+.1f}%)",
                "YoC (12m)": f"{fmt_num(yoc)}%",
                "Proventos Est. (Ano)": f"R$ {fmt_num(qtd * dpa_12m)}",
                "PT Bazin (12m)": f"R$ {fmt_num(dpa_12m / 0.06)}" if dpa_12m > 0 else "—",
            })

        lucro_tot = total_atual - total_investido
        lucro_tot_pct = ((total_atual / total_investido) - 1) * 100 if total_investido > 0 else 0.0
        yoc_cart = (renda_12m_est / total_investido) * 100 if total_investido > 0 else 0.0

        m1, m2, m3, m4 = st.columns(4)
        m1.metric("Total Investido", f"R$ {fmt_num(total_investido)}")
        m2.metric("Patrimônio Atual", f"R$ {fmt_num(total_atual)}", f"R$ {fmt_num(lucro_tot)} ({lucro_tot_pct:+.1f}%)")
        m3.metric("Renda Anual Est. (12m)", f"R$ {fmt_num(renda_12m_est)}", f"YoC Carteira: {fmt_num(yoc_cart)}%")
        m4.metric("Renda Anual Projetiva", f"R$ {fmt_num(renda_proj_est)}", f"~R$ {fmt_num(renda_proj_est / 12)}/mês")

        col_tab_c, col_graf_c = st.columns([2.2, 1])
        with col_tab_c:
            df_c = pd.DataFrame(linhas_cart).drop(columns=["Valor_Num"])
            st.dataframe(df_c, use_container_width=True, hide_index=True)
        with col_graf_c:
            fig_pie = go.Figure(
                data=[go.Pie(
                    labels=[x["Ticker"] for x in linhas_cart],
                    values=[x["Valor_Num"] for x in linhas_cart],
                    hole=0.48,
                    textinfo="label+percent",
                )]
            )
            fig_pie.update_layout(
                title="Alocação por Ativo",
                height=320,
                margin=dict(l=10, r=10, t=40, b=10),
                paper_bgcolor="rgba(0,0,0,0)",
                showlegend=False,
            )
            st.plotly_chart(fig_pie, use_container_width=True)

st.divider()
st.caption("Aviso: Estudo quantitativo e educacional com dados obtidos via Fundamentus e Yahoo Finance. Não constitui recomendação oficial de compra ou venda.")
