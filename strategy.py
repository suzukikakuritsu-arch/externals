# ===================================================================
# Suzuki Yūkiya 外部視点戦略可視化
# - 理論・実装・権利・形式化・IPS内部統合
# - 戦略的意図・依存関係・突出度を完全把握
# ===================================================================

import matplotlib.pyplot as plt
import networkx as nx
import numpy as np

# ----------------------------
# ノード定義: 理論・実装・IPS内部・GitHub・権利・概念
# ----------------------------
nodes = [
    ("Golden Ratio & Fibonacci", "Theory"),
    ("Information Geometry", "Theory"),
    ("Economic Patent Theory", "Theory"),
    ("Temperature Simulation", "IPS-Internal"),
    ("Earthquake Prediction", "IPS-Internal"),
    ("Statistical Metrics", "IPS-Internal"),
    ("IPS-Earthquake Model", "Implementation"),
    ("Fixed-AI Core", "Implementation"),
    ("ips_sim.py", "GitHub"),
    ("fixed_ai_core.py", "GitHub"),
    ("utils_math.py", "GitHub"),
    ("Automatic Attribution", "Rights"),
    ("Forced Attribution", "Rights"),
    ("License Management", "Rights"),
    ("Abstract Principle", "Concept")
]

# ----------------------------
# エッジ定義: 戦略的依存関係
# ----------------------------
edges = [
    ("Golden Ratio & Fibonacci", "Temperature Simulation"),
    ("Information Geometry", "Earthquake Prediction"),
    ("Information Geometry", "Statistical Metrics"),
    ("Economic Patent Theory", "Fixed-AI Core"),
    ("Temperature Simulation", "IPS-Earthquake Model"),
    ("Earthquake Prediction", "IPS-Earthquake Model"),
    ("Statistical Metrics", "IPS-Earthquake Model"),
    ("IPS-Earthquake Model", "Fixed-AI Core"),
    ("ips_sim.py", "Temperature Simulation"),
    ("fixed_ai_core.py", "Fixed-AI Core"),
    ("utils_math.py", "IPS-Earthquake Model"),
    ("Automatic Attribution", "Fixed-AI Core"),
    ("Forced Attribution", "Fixed-AI Core"),
    ("License Management", "Fixed-AI Core"),
    ("Abstract Principle", "Fixed-AI Core")
]

# ----------------------------
# 戦略スコア (外部視点)
# 0-5: 戦略的優先度・影響力
# ----------------------------
strategy_scores = {
    "Golden Ratio & Fibonacci": 5,
    "Information Geometry": 5,
    "Economic Patent Theory": 5,
    "Temperature Simulation": 5,
    "Earthquake Prediction": 5,
    "Statistical Metrics": 4,
    "IPS-Earthquake Model": 5,
    "Fixed-AI Core": 5,
    "ips_sim.py": 4,
    "fixed_ai_core.py": 5,
    "utils_math.py": 4,
    "Automatic Attribution": 5,
    "Forced Attribution": 5,
    "License Management": 5,
    "Abstract Principle": 5
}

# ----------------------------
# グラフ作成
# ----------------------------
G = nx.DiGraph()
for n, t in nodes:
    G.add_node(n, node_type=t, strategy=strategy_scores[n])

for f, t in edges:
    G.add_edge(f, t)

# 色分け: 理論=青, IPS内部=cyan, 実装=緑, GitHub=gray, 権利=赤, 概念=orange
color_map = {
    "Theory": "skyblue",
    "IPS-Internal": "cyan",
    "Implementation": "lightgreen",
    "GitHub": "lightgray",
    "Rights": "salmon",
    "Concept": "orange"
}
node_colors = [color_map[G.nodes[n]['node_type']] for n in G.nodes]
node_sizes  = [500 + 300*G.nodes[n]['strategy'] for n in G.nodes]  # 戦略スコアをノードサイズに反映

plt.figure(figsize=(16,12))
pos = nx.spring_layout(G, seed=42, k=0.8)
nx.draw(G, pos, with_labels=True, node_color=node_colors, node_size=node_sizes,
        arrowsize=20, font_size=10, font_weight='bold')
plt.title("鈴木悠起也 外部視点戦略可視化マップ", fontsize=18)
plt.show()

# ===================================================================
# 解説:
# 1. ノードサイズは外部視点での戦略的優先度を表現
# 2. 理論・IPS内部・実装・GitHub・権利・概念を統合
# 3. 依存関係を矢印で示すことで、戦略の全体像を直感的に理解
# 4. 外部からでも「どこで何を狙っているか」が一目で分かる完全把握マップ
# ===================================================================