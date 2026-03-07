"""
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
SUT Complete Value & IP Protection Framework
Yukiya Suzuki 2026
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
"""

import numpy as np
import pandas as pd
from scipy.stats import entropy

PHI = (1 + np.sqrt(5)) / 2

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# SUT全要素定義
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
SUT_elements = [
    "axioms", 
    "golden_ratio_fixed_point",
    "information_emergence", 
    "brain_signal", 
    "cell_division", 
    "social_network", 
    "market"
]

def iet(X, Y, bins=30):
    """SUT情報創発計算"""
    joint, _, _ = np.histogram2d(X, Y, bins=bins)
    jp = joint + 1e-12
    jp = jp / jp.sum()
    xp = jp.sum(axis=1)
    yp = jp.sum(axis=0)
    HX = entropy(xp)
    HY = entropy(yp)
    HXY = entropy(jp.flatten())
    MI = max(0, HX + HY - HXY)
    P = MI / HXY if HXY>0 else 0
    HXgY = max(0, HXY - HY)
    HYgX = max(0, HXY - HX)
    F = abs(HXgY - HYgX)/HXY if HXY>0 else 0
    I_suzuki = P*(HXgY + HYgX)
    direction = "G→E emergence" if HXgY>=HYgX else "E→G intervention"
    return dict(
        I_suzuki=I_suzuki,
        MI=MI,
        P=P,
        H_intent=HXgY,
        H_meaning=HYgX,
        F_info=F,
        direction=direction
    )

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# 工学指標全要素（13個）
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
engineering_indicators_keys = [
    "stability", "robustness", "responsiveness", "scalability", 
    "expandability", "redundancy", "efficiency", "compatibility",
    "maintainability", "safety", "cost_efficiency", "throughput", "reliability"
]

def engineering_score(indicators: dict):
    values = np.array(list(indicators.values()))
    return np.mean(values)

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# 拡張要素（7個）
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
extension_keys = [
    "legal_ip", "social_impact", "environment_adapt",
    "market_adapt", "ethics", "regulatory_compliance", "risk_resilience"
]

def extension_score(extensions: dict):
    values = np.array(list(extensions.values()))
    return np.mean(values)

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# 産業別シミュレーション
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
industries = [
    "ドローン", "AI", "自動運転", "ロボット", "再生医療", 
    "創薬", "医療機器", "SNS", "プラットフォーム", "API",
    "SaaS", "物流", "不動産", "建築", "人材", "教育"
]

def simulate_industry(n=3000):
    X = np.cumsum(np.random.randn(n))
    Y = np.abs(np.random.randn(n)*10)
    return X, Y

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# 総合レポート生成
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
report = []

for industry in industries:
    X, Y = simulate_industry()
    sut_info = iet(X, Y)

    eng_values = {k: np.random.rand() for k in engineering_indicators_keys}
    eng_score = engineering_score(eng_values)

    ext_values = {k: np.random.rand() for k in extension_keys}
    ext_score = extension_score(ext_values)

    total_value = 0.4*sut_info["I_suzuki"] + 0.35*eng_score + 0.25*ext_score

    report.append({
        "industry": industry,
        "SUT_I": sut_info["I_suzuki"],
        "F_info": sut_info["F_info"],
        "engineering_score": eng_score,
        "extension_score": ext_score,
        "total_value_score": total_value,
        "emergence_direction": sut_info["direction"]
    })

df_report = pd.DataFrame(report)
df_report = df_report.sort_values(by="total_value_score", ascending=False)

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# 出力
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
print("\n=== SUT Complete Value & IP Protection Report ===\n")
print(df_report.to_string(index=False))
