import math
from datetime import datetime, timedelta
import pandas as pd
import streamlit as st
import yfinance as yf

st.set_page_config(page_title="Painel Valuation B3", page_icon="📈", layout="wide")

DEFAULT_TICKERS = ["BBAS3", "BBDC3", "BBSE3", "CMIG4", "CSMG3", "CXSE3", "ITSA4", "TAEE11"]


def parse_tickers(raw: str) -> list[str]:
    itens = [x.strip().upper().replace(".SA", "") for x in raw.replace("\n", ",").split(",")]
    # Remove duplicados mantendo a ordem
    vistos = []
    for t in itens:
        if t and t not in vistos:
            vistos.append(t)
    return vistos


@st.cache_data(ttl=900, show_spinner=False)
def buscar_dados_ativo(ticker: str) -> dict:
    sa_ticker = f"{ticker}.SA"
    tk = yf.Ticker(sa_ticker)
    info = tk.info or {}

    # Cotação atual
    cotacao = info.get("currentPrice") or info.get("regularMarketPrice")
    if not cotacao:
        hist = tk.history(period="5d")
        if not hist.empty:
            cotacao = float(hist["Close"].iloc[-1])

    if not cotacao or cotacao <= 0:
        return {"erro": f"Não foi possível obter cotação para {ticker}."}

    nome = info.get("shortName") or info.get("longName") or ticker
    lpa = info.get("trailingEps")
    vpa = info.get("bookValue")
    pl = info.get("trailingPE") or (cotacao / lpa if lpa and lpa > 0 else None)
    pvp = info.get("priceToBook") or (cotacao / vpa if vpa and vpa > 0 else None)
    roe_raw = info.get("returnOnEquity")
    roe = roe_raw * 100 if roe_raw is not None else None

    # Histórico de dividendos
    divs = tk.dividends
    dpa_12m = 0.0
    dpa_med_6a = 0.0
    anos_hist = 0

    if divs is not None and not divs.empty:
        divs.index = pd.to_datetime(divs.index).tz_localize(None)
        hoje = pd.Timestamp.now().tz_localize(None)

        # Últimos 12 meses
        inicio_12m = hoje - timedelta(days=365)
        dpa_12m = float(divs[divs.index >= inicio_12m].sum())

        # Últimos 6 anos completos (ou máximo disponível até 6 anos)
        ano_atual = hoje.year
        anos_validos = [a for a in range(ano_atual - 6, ano_atual)]
        divs_6a = divs[divs.index.year.isin(anos_validos)]
        if not divs_6a.empty:
            por_ano = divs_6a.groupby(divs_6a.index.year).sum()
            anos_hist = len(por_ano)
            # Se tiver menos de 6 anos de bolsa, divide pelos anos encontrados
            divisor = min(6, max(1, anos_hist))
            dpa_med_6a = float(divs_6a.sum() / divisor)

    dy_12m = (dpa_12m / cotacao) * 100 if cotacao > 0 else 0.0

    # Estimativa automática de DPA Projetivo (LPA x Payout ou dividendRate)
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


def fmt_preco_ms(preco_calc: float | None, cotacao: float, sufixo: str = "") -> str:
    if preco_calc is None or preco_calc <= 0:
        return "N/A"
    ms = calc_ms(preco_calc, cotacao)
    sinal = "+" if ms >= 0 else ""
    tag = "🟢 (abaixo)" if cotacao <= preco_calc else "🔴 (acima)"
    return f"R$ {preco_calc:,.2f}{sufixo} | {sinal}{ms:.1f}% {tag}".replace(",", "X").replace(".", ",").replace("X", ".")


def calcular_score(d: dict, pt_med: float, pt_proj: float, pt_bazin: float, graham: float | None) -> tuple[float, list[str]]:
    cot = d["cotacao"]
    ms_lista = [x for x in [calc_ms(pt_med, cot), calc_ms(pt_proj, cot), calc_ms(pt_bazin, cot), calc_ms(graham, cot)] if x is not None]

    # 1. Margem de segurança média (até 45 pts)
    if ms_lista:
        ms_limitadas = [max(-40.0, min(60.0, m)) for m in ms_lista]
        avg_ms = sum(ms_limitadas) / len(ms_limitadas)
        pts_ms = max(0.0, min(45.0, ((avg_ms + 40.0) / 100.0) * 45.0))
    else:
        avg_ms = -40.0
        pts_ms = 0.0

    # 2. P/VP (até 20 pts; bônus se < 1)
    pvp = d["pvp"]
    if pvp is not None and pvp > 0:
        pts_pvp = max(0.0, min(15.0, ((2.5 - pvp) / 1.5) * 15.0)) + (5.0 if pvp < 1.0 else 0.0)
    else:
        pts_pvp = 0.0

    # 3. P/L (até 15 pts)
    pl = d["pl"]
    if pl is not None and pl > 0:
        pts_pl = max(0.0, min(15.0, ((20.0 - pl) / 15.0) * 15.0))
    else:
        pts_pl = 0.0

    # 4. ROE (até 20 pts)
    roe = d["roe"]
    if roe is not None and roe > 0:
        pts_roe = min(20.0, (roe / 25.0) * 20.0)
    else:
        pts_roe = 0.0

    score = round(pts_ms + pts_pvp + pts_pl + pts_roe, 1)

    motivos = []
    if ms_lista:
        real_avg = sum(ms_lista) / len(ms_lista)
        if real_avg > 15:
            motivos.append(f"forte desconto médio ({real_avg:+.1f}%) nos métodos")
        elif real_avg > 0:
            motivos.append(f"margem de segurança média positiva ({real_avg:+.1f}%)")
        else:
            motivos.append(f"negociada acima da média dos preços-teto ({real_avg:+.1f}%)")

    if pvp is not None:
        if pvp < 1:
            motivos.append(f"P/VP descontado abaixo do valor patrimonial ({pvp:.2f})")
        elif pvp > 1.8:
            motivos.append(f"P/VP esticado ({pvp:.2f})")

    if roe is not None:
        if roe >= 15:
            motivos.append(f"ROE forte ({roe:.1f}%)")
        elif roe < 8:
            motivos.append(f"ROE baixo ({roe:.1f}%)")

    if pl is not None and pl < 0:
        motivos.append("atenção: lucro negativo (P/L negativo)")

    return score, motivos


# --- INTERFACE ---
st.title("📊 Painel Pessoal de Valuation — B3")
st.caption("Preços-Teto (Médio 6a, Projetivo, Bazin), Preço Justo (Graham) e Ranking de Atratividade")

# Recupera ativos salvos na URL (?tickers=...) ou usa padrão
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
    st.caption("💡 Dica: ao atualizar a lista, o link do navegador muda automaticamente. Salve nos Favoritos para manter sua carteira salva!")

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

# Ajuste opcional do DPA Projetivo pelo usuário
with st.expander("✏️ Opcional: ajustar manualmente o DPA Projetivo (R$ por ação no ano)"):
    st.caption("Por padrão, o sistema estima o DPA Projetivo usando LPA × Payout. Se quiser usar a sua própria projeção (estilo AGF+), edite abaixo:")
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

# Monta tabela e ranking
linhas = []
ranking = []
data_ref = datetime.now().strftime("%d/%m/%Y %H:%M")

for d in dados_ativos:
    cot = d["cotacao"]
    dpa_proj = dpa_proj_custom[d["ticker"]]

    pt_med = d["dpa_med_6a"] / 0.06 if d["dpa_med_6a"] > 0 else None
    pt_proj = dpa_proj / 0.06 if dpa_proj > 0 else None
    pt_bazin = d["dpa_12m"] / 0.06 if d["dpa_12m"] > 0 else None
    graham = math.sqrt(22.5 * d["lpa"] * d["vpa"]) if (d["lpa"] and d["vpa"] and d["lpa"] > 0 and d["vpa"] > 0) else None

    pvp_str = f"{d['pvp']:.2f} {'🟢' if d['pvp'] < 1 else '🔴'}" if d["pvp"] is not None else "N/A"
    pl_str = f"{d['pl']:.2f}" if d["pl"] is not None else "N/A"
    roe_str = f"{d['roe']:.1f}%" if d["roe"] is not None else "N/A"

    lpa_str = f"R$ {d['lpa']:.2f}" if d["lpa"] is not None else "N/A"
    vpa_str = f"R$ {d['vpa']:.2f}" if d["vpa"] is not None else "N/A"

    sufixo_6a = "*" if 0 < d["anos_hist"] < 6 else ""

    linhas.append({
        "Ticker / Empresa": f"{d['ticker']} — {d['nome']}",
        f"Cotação ({data_ref}) & DY": f"R$ {cot:.2f} | DY {d['dy_12m']:.2f}%",
        "Indicadores (P/L | P/VP | ROE)": f"P/L: {pl_str} | P/VP: {pvp_str} | ROE: {roe_str}",
        "Dados Base (LPA | VPA | DPA 12m | 6a | Proj)": (
            f"LPA: {lpa_str} | VPA: {vpa_str} | "
            f"12m: R$ {d['dpa_12m']:.2f} | 6a: R$ {d['dpa_med_6a']:.2f} | Proj: R$ {dpa_proj:.2f}"
        ),
        "Preço Teto Médio (6a) & MS": fmt_preco_ms(pt_med, cot, sufixo_6a),
        "Preço Teto Projetivo & MS": fmt_preco_ms(pt_proj, cot),
        "Preço-Teto Bazin (12m) & MS": fmt_preco_ms(pt_bazin, cot),
        "Preço Justo Graham & MS": fmt_preco_ms(graham, cot),
    })

    score, motivos = calcular_score(d, pt_med or 0, pt_proj or 0, pt_bazin or 0, graham)
    ranking.append({
        "ticker": d["ticker"],
        "nome": d["nome"],
        "cotacao": cot,
        "score": score,
        "motivos": motivos,
    })

st.subheader("1. Resumo de Cotações e Tabela Comparativa")
df = pd.DataFrame(linhas)
st.dataframe(df, use_container_width=True, hide_index=True)
st.caption("*Nota: ativos com asterisco (*) possuem menos de 6 anos completos de histórico de proventos no Yahoo Finance.*")

st.subheader("2. Ranking de Atratividade (Mais recomendável → Menos recomendável)")
ranking.sort(key=lambda x: x["score"], reverse=True)

for pos, item in enumerate(ranking, start=1):
    justificativa = "; ".join(item["motivos"]).capitalize() + "." if item["motivos"] else "Sem dados suficientes para justificativa."
    st.markdown(
        f"**{pos}º Lugar: {item['ticker']}** ({item['nome']}) | "
        f"**Cotação Atual: R$ {item['cotacao']:.2f}** | "
        f"**Score: {item['score']}/100**  \n"
        f"_{justificativa}_"
    )

st.divider()
st.caption("Aviso: Estudo quantitativo e educacional com dados obtidos via Yahoo Finance. Pode haver pequenas diferenças de centavos em JCP/proventos em relação ao RI das empresas. Não constitui recomendação oficial de compra ou venda.")
