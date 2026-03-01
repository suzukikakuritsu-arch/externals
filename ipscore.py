# ===================================================================
# Suzuki Yūkiya Project: 超詳細可視化マップ
# - IPSモデル内部データフロー + GitHub依存関係統合
# - 理論・実装・権利・抽象概念まで完全統合
# ===================================================================

import matplotlib.pyplot as plt
import networkx as nx

# ----------------------------
# ノード定義: 理論 / 実装 / IPS内部 / GitHubファイル / 権利 / 概念
# ----------------------------
nodes = [
    # 理論層
    ("Golden Ratio & Fibonacci", "Theory"),
    ("Information Geometry", "Theory"),
    ("Economic Patent Theory", "Theory"),
    # IPS内部層
    ("Temperature Simulation", "IPS-Internal"),
    ("Earthquake Prediction", "IPS-Internal"),
    ("Statistical Metrics", "IPS-Internal"),
    # 実装層
    ("IPS-Earthquake Model", "Implementation"),
    ("Fixed-AI Core", "Implementation"),
    # GitHubファイル層
    ("ips_sim.py", "GitHub"),
    ("fixed_ai_core.py", "GitHub"),
    ("utils_math.py", "GitHub"),
    # 権利層
    ("Automatic Attribution", "Rights"),
    ("Forced Attribution", "Rights"),
    ("License Management", "Rights"),
    # 抽象概念
    ("Abstract Principle", "Concept")
]

# ----------------------------
# エッジ定義: 依存関係
# ----------------------------
edges = [
    # 理論→IPS内部
    ("Golden Ratio & Fibonacci", "Temperature Simulation"),
    ("Information Geometry", "Earthquake Prediction"),
    ("Information Geometry", "Statistical Metrics"),
    ("Economic Patent Theory", "Fixed-AI Core"),
    # IPS内部→実装
    ("Temperature Simulation", "IPS-Earthquake Model"),
    ("Earthquake Prediction", "IPS-Earthquake Model"),
    ("Statistical Metrics", "IPS-Earthquake Model"),
    ("IPS-Earthquake Model", "Fixed-AI Core"),
    # GitHub実装対応
    ("ips_sim.py", "Temperature Simulation"),
    ("fixed_ai_core.py", "Fixed-AI Core"),
    ("utils_math.py", "IPS-Earthquake Model"),
    # 権利→実装
    ("Automatic Attribution", "Fixed-AI Core"),
    ("Forced Attribution", "Fixed-AI Core"),
    ("License Management", "Fixed-AI Core"),
    # 抽象概念→実装
    ("Abstract Principle", "Fixed-AI Core")
]

# ----------------------------
# グラフ作成
# ----------------------------
G = nx.DiGraph()
for n, t in nodes:
    G.add_node(n, node_type=t)

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

plt.figure(figsize=(16,12))
pos = nx.spring_layout(G, seed=42, k=0.8)  # 自動配置・ノード間距離調整
nx.draw(G, pos, with_labels=True, node_color=node_colors, node_size=2200,
        arrowsize=20, font_size=10, font_weight='bold')
plt.title("Suzuki Yūkiya Project: 超詳細可視化マップ", fontsize=18)
plt.show()

# ===================================================================
# 解説:
# 1. 理論層→IPS内部→実装層→GitHubファイル層→権利層の全フローを可視化
# 2. IPS内部ノード（温度シミュ・地震予測・統計指標）まで追跡可能
# 3. 各ノードの色分けで層構造が一目で理解可能
# 4. 外部視点からでも鈴木悠起也プロジェクトの完全構造を追える
# ===================================================================