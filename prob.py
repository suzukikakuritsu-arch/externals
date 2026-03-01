import numpy as np
import matplotlib.pyplot as plt

# パラメータ
num_attractors = 10
dim = 3          # 可視化用に低次元
time_steps = 20

# --- 抽象的確率分布の生成 ---
# 各アトラクターに対する収束確率をランダムでフラクタル風に生成
np.random.seed(42)
def generate_probabilities(num_attractors, time_steps):
    base = np.random.rand(num_attractors)
    base /= base.sum()  # 正規化
    probs = np.zeros((time_steps, num_attractors))
    for t in range(time_steps):
        # 時間変化で微小摂動
        perturb = np.random.normal(scale=0.05, size=num_attractors)
        probs[t] = base + perturb
        probs[t] = np.clip(probs[t], 0, None)
        probs[t] /= probs[t].sum()
    return probs

probs = generate_probabilities(num_attractors, time_steps)

# --- ヒートマップ作成 ---
plt.figure(figsize=(10, 6))
plt.imshow(probs, cmap='viridis', aspect='auto')
plt.colorbar(label='Convergence Probability')
plt.xlabel('Attractor Index')
plt.ylabel('Time Step')
plt.title('Observer Convergence Heatmap in Fractal Universe')
plt.show()
