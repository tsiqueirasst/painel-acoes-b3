import html
import math
from datetime import datetime, timedelta, timezone
import pandas as pd
import streamlit as st
import yfinance as yf

st.set_page_config(page_title="Painel Valuation B3", page_icon="📈", layout="wide")

BRT = timezone(timedelta(hours=-3))
DEFAULT_TICKERS = ["CMIG4", "BBDC3", "BBAS3", "SANB11", "ISAE4", "TAEE11", "CSMG3", "SAPR4", "PETR4", "EGIE3"]


def parse_tickers(raw: str) -> list[str]:
    itens = [x.strip().upper().replace(".SA", "") for x in raw.replace("\n", ",").split(",")]
    vistos = []
    for t in itens:
        if t and t not in vistos:
            vistos.append(t)
    return vistos


def fmt_num(val: float, casas: int = 2) -> str:
    s = f"{val:,.{casas}f}"
    return s.replace(",", "X").replace(".", ",").replace("X", ".")


@st.cache_data(ttl=900, show_spinner=False)
def buscar_dados_ativo(ticker: str) -> dict:
    sa_ticker = f"{ticker}.SA"
    tk = yf.Ticker(sa_ticker)
    info = tk.info or {}

    cotacao = info.get("currentPrice") or info.get("regularMarketPrice")
    if not cotacao:
        hist = tk.history(period="5d")
        if not hist.empty:
            cotacao = float(hist["Close"].iloc[-1])

    if not cotacao or cotacao <= 0:
        return {"erro": f"Não foi possível obter cotação para {ticker}."}

    nome_raw = info.get("shortName") or info.get("longName") or ticker
    nome = " ".join(nome_raw.split())
    lpa = info.get("trailingEps")
    vpa = info.get("bookValue")
    pl = info.get("trailingPE") or (cotacao / lpa if lpa and lpa > 0 else None)
    pvp = info.get("priceToBook") or (cotacao / vpa if vpa and vpa > 0 else None)

    roe_raw = info.get("returnOnEquity")
    if roe_raw is not None:
        roe = roe_raw * 100
    elif lpa is not None and vpa is not None and vpa > 0:
        roe = (lpa / vpa) * 100
    else:
        roe = None

    divs = tk.dividends
    dpa_12m = 0.0
    dpa_med_6a = 0.0
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

    dy_12m = (dpa_12m / cotacao) * 100 if cotacao > 0 else 0.0

    payout = info.get("payoutRatio")
    div_rate = info.get("dividendRate")
    if lpa and lpa > 0 and payout and 0 < payout <= 1.2:
        dpa_proj = float(lpa * min(payout, 1.0))
    elif div_rate and div_rate > 0:
        dpa_proj = float(div_rate)
    else:
        dpa_proj = dpa_12m

    return {
        "ticker": ticker,
        "nome": nome,
        "cotacao": float(cotacao),
        "dy_12m": float(dy_12m),
        "pl": float(pl) if pl is not None else None,
        "pvp": float(pvp) if pvp is not None else None,
        "roe": float(roe) if roe is not None else None,
        "lpa": float(lpa) if lpa is not None else None,
        "vpa": float(vpa) if vpa is not None else None,
        "dpa_12m": float(dpa_12m),
        "dpa_med_6a": float(dpa_med_6a),
        "anos_hist": anos_hist,
        "dpa_proj": float(dpa_proj),
    }


def calc_ms(preco_calc: float | None, cotacao: float) -> float | None:
    if preco_calc is None or preco_calc <= 0:
        return None
    return ((preco_calc - cotacao) / preco_calc) * 100


def html_preco_ms(preco_calc: float | None, cotacao: float, sufixo: str = "") -> str:
    if preco_calc is None or preco_calc <= 0:
        return "<span style='opacity:0.6;'>N/A</span>"
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
            motivos.append(f"P/VP descontado abaixo do patrimônio ({fmt_num(pvp)})")
        elif pvp > 1.8:
            motivos.append(f"P/VP esticado ({fmt_num(pvp)})")

    if roe is not None:
        if roe >= 15:
            motivos.append(f"ROE forte ({fmt_num(roe, 1)}%)")
        elif roe < 8:
            motivos.append(f"ROE baixo ({fmt_num(roe, 1)}%)")

    if pl is not None and pl < 0:
        motivos.append("atenção: lucro negativo (P/L negativo)")

    return score, avg_ms_real, motivos


# --- INTERFACE ---
st.title("📊 Painel Pessoal de Valuation — B3")
st.caption("Preços-Teto (Médio 6a, Projetivo, Bazin), Preço Justo (Graham), Comparador e Ranking Automático")

tickers_url = st.query_params.get("tickers", ",".join(DEFAULT_TICKERS))

with st.sidebar:
    st.header("⚙️ Seus Ativos")
    entrada = st.text_area(
        "Digite os tickers separados por vírgula:",
        value=tickers_url,
        height=120,
        help="Exemplo: BBAS3, BBDC3, BBSE3, TAEE11"
    )
    if st.button("🔄 Atualizar Dados", type="primary", use_container_width=True):
        st.cache_data.clear()

    tickers = parse_tickers(entrada)
    if tickers:
        st.query_params["tickers"] = ",".join(tickers)
    st.caption("💡 Dica: ao alterar a lista, salve o link atualizado nos Favoritos para manter sua carteira salva.")

if not tickers:
    st.warning("Adicione pelo menos um ticker na barra lateral.")
    st.stop()

dados_ativos = []
erros = []
with st.spinner("Buscando cotações e fundamentos na B3..."):
    for t in tickers:
        res = buscar_dados_ativo(t)
        if "erro" in res:
            erros.append(res["erro"])
        else:
            dados_ativos.append(res)

for e in erros:
    st.error(e)

if not dados_ativos:
    st.stop()

with st.expander("✏️ Opcional: ajustar manualmente o DPA Projetivo (R$ por ação no ano)"):
    st.caption("Por padrão, o sistema estima o DPA Projetivo usando LPA × Payout. Se quiser usar sua própria projeção (estilo AGF+), edite abaixo:")
    cols_proj = st.columns(min(4, len(dados_ativos)))
    dpa_proj_custom = {}
    for i, d in enumerate(dados_ativos):
        with cols_proj[i % len(cols_proj)]:
            dpa_proj_custom[d["ticker"]] = st.number_input(
                f"{d['ticker']}",
                min_value=0.0,
                value=round(d["dpa_proj"], 2),
                step=0.05,
                format="%.2f",
            )

# Calcula tudo e ordena do melhor Score para o pior
resultados = []
data_ref = datetime.now(BRT).strftime("%d/%m/%Y %H:%M")

for d in dados_ativos:
    cot = d["cotacao"]
    dpa_proj = dpa_proj_custom[d["ticker"]]
    pt_med = d["dpa_med_6a"] / 0.06 if d["dpa_med_6a"] > 0 else None
    pt_proj = dpa_proj / 0.06 if dpa_proj > 0 else None
    pt_bazin = d["dpa_12m"] / 0.06 if d["dpa_12m"] > 0 else None
    graham = math.sqrt(22.5 * d["lpa"] * d["vpa"]) if (d["lpa"] and d["vpa"] and d["lpa"] > 0 and d["vpa"] > 0) else None
    score, avg_ms, motivos = calcular_score(d, pt_med, pt_proj, pt_bazin, graham)

    resultados.append({
        **d,
        "dpa_proj_usado": dpa_proj,
        "pt_med": pt_med,
        "pt_proj": pt_proj,
        "pt_bazin": pt_bazin,
        "graham": graham,
        "score": score,
        "avg_ms": avg_ms,
        "motivos": motivos,
    })

resultados.sort(key=lambda x: x["score"], reverse=True)

tab1, tab2 = st.tabs(["📊 Ranking & Tabela Geral", "⚖️ Comparar Ativos"])

with tab1:
    st.subheader("1. Resumo de Cotações e Tabela (Ordenada do mais recomendável ao menos recomendável)")

    linhas_html = []
    for pos, r in enumerate(resultados, start=1):
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
        nome_esc = html.escape(r["nome"])

        linhas_html.append(f"""
        <tr>
            <td style="text-align:center; font-weight:700;">{pos}º<br><small style="opacity:0.75;">{r['score']}</small></td>
            <td><strong>{r['ticker']}</strong><br><small style="opacity:0.75;">{nome_esc}</small></td>
            <td><strong>R$ {fmt_num(cot)}</strong><br><small>DY: {fmt_num(r['dy_12m'])}%</small></td>
            <td>P/L: {pl_txt}<br>P/VP: {pvp_html}<br>ROE: {roe_txt}</td>
            <td>LPA: {lpa_txt} | VPA: {vpa_txt}<br>12m: R$ {fmt_num(r['dpa_12m'])} | 6a: R$ {fmt_num(r['dpa_med_6a'])}<br>Proj: R$ {fmt_num(r['dpa_proj_usado'])}</td>
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
            line-height: 1.45;
        }}
        .val-table th {{
            background-color: rgba(128, 128, 128, 0.18);
            text-align: left;
            padding: 9px 7px;
            border-bottom: 2px solid rgba(128, 128, 128, 0.35);
            font-weight: 600;
            font-size: 12px;
        }}
        .val-table td {{
            padding: 9px 7px;
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
                    <th style="text-align:center;">Pos.<br><small>Score</small></th>
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
    st.caption("Nota: ativos com asterisco (*) possuem menos de 6 anos completos de histórico de proventos no Yahoo Finance.")

    st.subheader("2. Justificativas do Ranking")
    for pos, r in enumerate(resultados, start=1):
        justificativa = "; ".join(r["motivos"]).capitalize() + "." if r["motivos"] else "Sem dados suficientes para justificativa."
        st.markdown(
            f"**{pos}º Lugar: {r['ticker']}** ({r['nome']}) | "
            f"**Cotação Atual: R$ {fmt_num(r['cotacao'])}** | "
            f"**Score: {r['score']}/100**  \n"
            f"_{justificativa}_"
        )

with tab2:
    st.subheader("⚖️ Comparador Lado a Lado")
    opcoes = [r["ticker"] for r in resultados]
    selecionados = st.multiselect(
        "Escolha 2 ou mais ativos para comparar:",
        options=opcoes,
        default=opcoes[:min(3, len(opcoes))],
    )

    if len(selecionados) < 2:
        st.info("Selecione pelo menos 2 ativos acima para visualizar a comparação.")
    else:
        itens_comp = [r for r in resultados if r["ticker"] in selecionados]

        cols = st.columns(min(4, len(itens_comp)))
        for idx, r in enumerate(itens_comp):
            with cols[idx % len(cols)]:
                with st.container(border=True):
                    pos_geral = next(i for i, x in enumerate(resultados, 1) if x["ticker"] == r["ticker"])
                    st.markdown(f"### {r['ticker']} ({pos_geral}º no geral)")
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
st.caption("Aviso: Estudo quantitativo e educacional com dados obtidos via Yahoo Finance. Pode haver pequenas diferenças de centavos em JCP/proventos em relação ao RI das empresas. Não constitui recomendação oficial de compra ou venda.")
