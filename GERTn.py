# N状態GERT：一般化理論
def general_n_gert(n_states):
    """
    N状態GER系：
    X_{i+1} = αX_i + βX_{i-1} + γlog(1+X_{i+1})
    """
    # 安定性P_N(δ) ∝ N/(N+δ/σ)
    # 堅牢性R_N(δ) ∝ δ/(δ+1/N)
    # S_N(δ) = P_N・R_N → δ*_N = σ√N
    
    sigma = 0.04
    delta_star_N = sigma * np.sqrt(n_states)
    return delta_star_N

# 3状態（GER）：δ*=0.236
print(f"N=3: δ* = {general_n_gert(3):.4f}")

# 高次元：N=10,100
print(f"N=10: δ* = {general_n_gert(10):.4f}")
print(f"N=100: δ* = {general_n_gert(100):.4f}")
