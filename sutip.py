import numpy as np

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# UNIVERSAL INTELLECTUAL PROPERTY VALUE
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def universal_ip_value(I_suzuki, F_info, V_rare,
                       novelty_weight=1.0,
                       scarcity_weight=1.0,
                       noise_std=0.1,
                       n_samples=1000):
    """
    幅を持たせた普遍的知財価値 V_IP 分布生成

    Parameters
    ----------
    I_suzuki : float
        情報創発量（基礎価値）
    F_info : float
        斥力・新規性（イノベーション度）
    V_rare : float
        希少価値乗数
    novelty_weight : float
        F_info に対する重み
    scarcity_weight : float
        V_rare に対する重み
    noise_std : float
        乱数ノイズ標準偏差（幅の表現）
    n_samples : int
        サンプル数（分布の幅を評価）

    Returns
    -------
    values : np.ndarray
        V_IP 分布サンプル
    V_mean : float
        平均値
    V_std : float
        標準偏差
    """
    if np.isinf(V_rare):
        return np.full(n_samples, np.inf), np.inf, 0.0

    # 正規ノイズで幅を表現
    noise = np.random.randn(n_samples) * noise_std

    # 基本 V_IP 計算
    base_value = I_suzuki * V_rare * (1 + novelty_weight * F_info) * scarcity_weight

    # サンプル分布
    values = base_value * (1 + noise)

    V_mean = np.mean(values)
    V_std  = np.std(values)

    return values, V_mean, V_std


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# EXAMPLE
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

if __name__ == "__main__":
    # ダミー値（IET創発、斥力、希少価値）
    I_s = 0.8
    F_info = 0.25
    V_rare = 2.0

    vals, mean, std = universal_ip_value(I_s, F_info, V_rare,
                                         novelty_weight=1.2,
                                         scarcity_weight=1.1,
                                         noise_std=0.15,
                                         n_samples=5000)

    print(f"平均 V_IP = {mean:.4f}, 標準偏差 = {std:.4f}")
    print(f"最小値={vals.min():.4f}, 最大値={vals.max():.4f}")
