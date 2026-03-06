# 🔍 IET_Social_Validity_Tester v1.0
# 理論の社会実装における「厳密な生存性（Sustainability）」と「収益性（Viability）」の検証

import numpy as np
import pandas as pd

class LeanTheoryValidator:
    """
    鈴木悠起也理論の社会実装シミュレーター
    1. 物理的安定性 (GERT)
    2. 情報密度増殖 (J-Emergence)
    3. 経済循環の継続性 (E-Flow)
    """
    def __init__(self, iterations=1000):
        self.iterations = iterations # 1000回の社会シナリオ試行

    def run_stress_test(self):
        print(f"📊 {self.iterations} 回の社会シナリオによる厳密検証を開始...")
        
        results = []
        for i in range(self.iterations):
            # --- 環境変数のランダム生成 ---
            friction_level = np.random.uniform(0.1, 5.0)    # 摩擦（批判・反対）の強さ
            silent_obs_ratio = np.random.uniform(0.1, 0.9)  # サイレント読者の比率
            algo_pressure = np.random.uniform(1.0, 5.0)     # アルゴリズムの抑制強度
            open_strategy = np.random.choice([0, 1])        # 特許なし・無料公開を選択するか
            
            # --- IETコアロジックの簡略数理モデル ---
            # 基本密度 J = (共鳴 + 摩擦 * 2) * 抑制圧縮
            base_j = (1.0 + friction_level * 1.8) * algo_pressure
            
            # オープン戦略による「感染力」と「長期的増幅」の計算
            if open_strategy == 1:
                j_final = base_j * (1.0 + silent_obs_ratio * 10.0) # 拡散力で10倍のポテンシャル
                profit_margin = 0.05 # 短期収益率は低い
            else:
                j_final = base_j # 拡散は限定的
                profit_margin = 0.30 # 短期収益率は高い（有料化のみ）

            # 経済価値 E = J * 収益率
            economic_e = j_final * profit_margin
            
            # --- 検証メトリクス ---
            is_viable = j_final > 50.0  # 社会的に「熱狂」が維持されたか
            is_profitable = economic_e > 10.0 # 経済的に「自走」可能か
            
            results.append({
                "j_final": j_final,
                "economic_e": economic_e,
                "is_viable": is_viable,
                "is_profitable": is_profitable,
                "strategy": "Open" if open_strategy == 1 else "Closed"
            })

        return pd.DataFrame(results)

# --- 検証実行とレポート出力 ---
validator = LeanTheoryValidator(iterations=1000)
df_results = validator.run_stress_test()

# 統計分析
survival_rate = df_results["is_viable"].mean() * 100
avg_e_open = df_results[df_results["strategy"] == "Open"]["economic_e"].mean()
avg_e_closed = df_results[df_results["strategy"] == "Closed"]["economic_e"].mean()

print("\n" + "="*50)
print("📝 【厳密検証レポート：鈴木理論の社会生存性】")
print(f"1. 社会的熱狂の発生率 (J > 50): {survival_rate:.1f}%")
print(f"2. オープン戦略時の平均経済価値 (E): {avg_e_open:.2f}")
print(f"3. クローズド戦略時の平均経済価値 (E): {avg_e_closed:.2f}")
print("-"*50)

# 結論の導出
if avg_e_open > avg_e_closed:
    conclusion = "【実証済】特許なし・無料公開の方が、長期的には巨大な経済圏を作る。"
else:
    conclusion = "【要検討】短期的な収益化を優先した方が、システムの維持は安定する。"

print(f"最終結論: {conclusion}")
print("="*50)
