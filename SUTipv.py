"""
SUT-IP Value 時間推移シミュレーション
- 産業別・製品別の知財・法務価値成長・減衰を追跡
- 創発情報 + 工学指標 + 社会的拡張 + 知財/特許スコア
- 労働価値説・効用説・古典生産価値と比較
"""

import numpy as np
import pandas as pd
from scipy.stats import entropy
import matplotlib.pyplot as plt

# ━━━━━━━━━━━━━━━━━━━━━
# 産業・製品設定
# ━━━━━━━━━━━━━━━━━━━━━
industries = [
    "ドローン","AI","自動運転","ロボット","再生医療",
    "創薬","医療機器","SNS","プラットフォーム","API",
    "SaaS","物流","不動産","建築","人材","教育"
]
products = ["製品A","製品B","サービスC","知財D"]

PHI = (1 + np.sqrt(5))/2  # 黄金比

# 工学指標サンプル（13個）
engineering_metrics = ["stability","robustness","responsiveness","scalability","efficiency",
                       "redundancy","modularity","safety","reliability","maintainability",
                       "portability","adaptability","cost_effectiveness"]

# シミュレーション期間
T = 10  # 年
np.random.seed(42)

# ━━━━━━━━━━━━━━━━━━━━━
# SUT-IP Value 時間推移関数
# ━━━━━━━━━━━━━━━━━━━━━
def sut_ip_time_series(industry_idx, product_idx, T):
    eng_base = np.random.rand(len(engineering_metrics))
    eng_score = eng_base.mean()
    
    values = []
    for t in range(T):
        # 創発情報の変化（ランダム変動＋成長）
        info = entropy(np.random.rand(50)) * (1 + 0.05*t)
        
        # 工学設計価値（少し安定して成長）
        eng = eng_score * (1 + 0.02*t)
        
        # 社会・法的拡張価値
        social = np.random.rand() * (1 + 0.03*t)
        
        # 知財・特許影響スコア（法務的価値、時間で強化・劣化）
        ip_score = np.clip(np.random.rand() + 0.05*t - 0.01*(t>5)*(t-5), 0, 1)  # 5年後劣化開始
        
        # 統合SUT-IP Value
        sut_ip_value = PHI*info + eng + social + ip_score
        
        # 他の経済理論
        labor_val = np.random.randint(1,101)
        utility_val = np.random.rand()*10
        classical_val = np.random.randint(1,50) + np.random.randint(1,50) + np.random.randint(1,50)
        
        values.append({
            "Year": t,
            "SUT-IP_value": sut_ip_value,
            "SUT_info": info,
            "SUT_engineering": eng,
            "SUT_social": social,
            "SUT_IPscore": ip_score,
            "Labor_value": labor_val,
            "Utility_value": utility_val,
            "Classical_production_value": classical_val
        })
        
    return pd.DataFrame(values)

# ━━━━━━━━━━━━━━━━━━━━━
# 全産業・全製品シミュレーション
# ━━━━━━━━━━━━━━━━━━━━━
time_series_data = {}

for i, industry in enumerate(industries):
    for j, product in enumerate(products):
        key = f"{industry}-{product}"
        time_series_data[key] = sut_ip_time_series(i,j,T)

# ━━━━━━━━━━━━━━━━━━━━━
# 可視化例: ドローン-製品A
# ━━━━━━━━━━━━━━━━━━━━━
df_plot = time_series_data["ドローン-製品A"]
plt.figure(figsize=(10,6))
plt.plot(df_plot["Year"], df_plot["SUT-IP_value"], label="SUT-IP Value", marker='o')
plt.plot(df_plot["Year"], df_plot["Labor_value"], label="Labor Value", marker='x')
plt.plot(df_plot["Year"], df_plot["Utility_value"], label="Utility Value", marker='s')
plt.plot(df_plot["Year"], df_plot["Classical_production_value"], label="Classical Production Value", marker='^')
plt.xlabel("Year")
plt.ylabel("Value")
plt.title("Time Evolution of SUT-IP vs Other Economic Values\n(ドローン-製品A)")
plt.legend()
plt.grid(True)
plt.show()
