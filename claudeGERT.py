# “””
GERT 安堅性解析 完全版

鈴木悠起也 × Claude  2026年3月

【今回の解析で確認できたこと】

1. GER不動点の解析解
1. ヤコビアン固有値 = GER係数 (0.95, 0.5)
1. 安堅性 S(δ) = P(δ) × R(δ) の正しい定義
1. δ* = (φ/10)×ln(2+√5) = 0.2336 の導出
1. 1/φ³=0.2361 との差 0.0025 (1.05%) の確認

【主張しないこと】

- δ*=0.236 との完全一致（1%の差がある）
- 「宇宙最強」「査読通過確定」等の未検証主張
  “””

import numpy as np
from scipy.optimize import brentq

phi = (1 + 5**0.5) / 2  # 黄金比 φ = 1.6180…

# =============================================================================

# 1. GER方程式（決定論版）

# =============================================================================

# G(t+1) = a × [G(t) + φ × r]

# E(t+1) = b × [E(t) + log(1 + G(t+1))] / (1/(1-b)+1) … 整理すると:

# E(t+1) = b × E(t) + (1-b) × log(1+G(t+1))  ← b=0.5 のとき平均

# 

# 実装上の等価形:

# E_new = 0.5*(E + log(1+G_new))

GER_PARAMS = {
‘a’: 0.95,   # Genesis 減衰
‘b’: 0.5,    # Emergence 蒸留
‘r’: 0.1,    # Reflux 還流率
‘phi’: phi,  # 黄金比（創世定数）
}

def ger_step(G, E, params=GER_PARAMS):
a, b, r, phi_ = params[‘a’], params[‘b’], params[‘r’], params[‘phi’]
G_new = a * (G + phi_ * r)
if G_new <= -1:
return None, None   # log の定義域外
E_new = b * (E + np.log(1 + G_new))
return G_new, E_new

# =============================================================================

# 2. 不動点の解析解

# =============================================================================

# G* = a×φ×r / (1-a)  （不動点方程式 G = a(G+φr) を解く）

# E* = log(1 + G*)     （不動点方程式 E = 0.5(E+log(1+G)) を解く → E=log(1+G)）

def fixed_point_analytic(params=GER_PARAMS):
a, r, phi_ = params[‘a’], params[‘r’], params[‘phi’]
G_star = a * phi_ * r / (1 - a)
E_star = np.log(1 + G_star)
S_star = G_star / E_star
return G_star, E_star, S_star

def fixed_point_numeric(params=GER_PARAMS, steps=10000):
G, E = 1.0, 0.5
for _ in range(steps):
G, E = ger_step(G, E, params)
return G, E, G/E

# =============================================================================

# 3. ヤコビアン固有値

# =============================================================================

# J = [[a,  0],

# [a/(2(1+G*)), b]]

# 固有値: λ₁=a=0.95, λ₂=b=0.5

# スペクトル半径 = 0.95 < 1 → 漸近安定

def jacobian_eigenvalues(params=GER_PARAMS):
a, b = params[‘a’], params[‘b’]
# 固有値は係数そのもの（解析的に導出可能）
return a, b   # λ₁, λ₂

# =============================================================================

# 4. 安堅性 S(δ) = P(δ) × R(δ)

# =============================================================================

# P(δ) = exp(-δ/α)         安定性: δ↑ → P↓（指数減衰）

# R(δ) = 1 - exp(-δ/β)     堅牢性: δ↑ → R↑（飽和増加）

# S(δ) = P(δ) × R(δ)       安堅性: トレードオフの積

# 

# GERの固有値との対応:

# α = 1 - λ₁ = 1 - a = 0.05   （Genesis の散逸速度）

# β = φ × r  = 1.618 × 0.1   （黄金比 × 還流率 = 0.1618）

def anken_params(params=GER_PARAMS):
alpha = 1 - params[‘a’]             # = 0.05
beta  = params[‘phi’] * params[‘r’] # = φ×0.1 = 0.1618
return alpha, beta

def P_stability(delta, alpha):
return np.exp(-delta / alpha)

def R_robustness(delta, beta):
return 1 - np.exp(-delta / beta)

def S_anken(delta, alpha, beta):
return P_stability(delta, alpha) * R_robustness(delta, beta)

# =============================================================================

# 5. 最適帯域幅 δ* の解析解

# =============================================================================

# dS/dδ = 0 を解くと:

# δ* = β × ln(1 + β/α)

# 

# α=0.05, β=φ/10 を代入:

# δ* = (φ/10) × ln(1 + 2φ)

# = (φ/10) × ln(2 + √5)     ← 1+2φ = 2+√5 = φ³

# = (φ/10) × arcsinh(2)

# = 0.23359

def delta_star_analytic(alpha, beta):
return beta * np.log(1 + beta / alpha)

# =============================================================================

# 実行・検証

# =============================================================================

if **name** == “**main**”:
print(”=” * 60)
print(“GERT 安堅性解析”)
print(”=” * 60)

```
# --- 不動点 ---
G_a, E_a, S_a = fixed_point_analytic()
G_n, E_n, S_n = fixed_point_numeric()
print("\n【不動点】")
print(f"  解析解: G*={G_a:.6f}, E*={E_a:.6f}, S*={S_a:.6f}")
print(f"  数値解: G*={G_n:.6f}, E*={E_n:.6f}, S*={S_n:.6f}")
print(f"  一致誤差: {abs(G_a-G_n):.2e}")

# --- 固有値 ---
lam1, lam2 = jacobian_eigenvalues()
print(f"\n【ヤコビアン固有値】")
print(f"  λ₁ = a = {lam1}  （Genesis 減衰）")
print(f"  λ₂ = b = {lam2}  （Emergence 蒸留）")
print(f"  スペクトル半径 = {max(lam1,lam2)} < 1 → 安定")

# --- 安堅性パラメータ ---
alpha, beta = anken_params()
print(f"\n【安堅性パラメータ】")
print(f"  α = 1-a   = {alpha:.5f}  （安定性の散逸速度）")
print(f"  β = φ×r   = {beta:.6f}  （堅牢性の飽和速度）")
print(f"  β/α       = {beta/alpha:.4f}  （≈ a/r = {GER_PARAMS['a']/GER_PARAMS['r']}）")

# --- δ* ---
ds = delta_star_analytic(alpha, beta)
target = 1 / phi**3
print(f"\n【最適帯域幅 δ*】")
print(f"  δ* = β×ln(1+β/α) = (φ/10)×ln(2+√5)")
print(f"     = {ds:.8f}")
print(f"  1/φ³             = {target:.8f}")
print(f"  差               = {abs(ds-target):.8f}  ({abs(ds-target)/target*100:.2f}%)")
print(f"  → 近似として成立するが等号ではない")

# --- 安堅性の形状 ---
print(f"\n【S(δ) の形状（α={alpha}, β={beta:.4f}）】")
print(f"  {'δ':>6} | {'P(δ)':>7} | {'R(δ)':>7} | {'S(δ)':>7}")
print(f"  {'-'*35}")
deltas = [0.05, 0.10, 0.15, 0.20, ds, 0.30, 0.40, 0.50]
for d in deltas:
    P = P_stability(d, alpha)
    R = R_robustness(d, beta)
    S = P * R
    marker = " ← δ*" if abs(d - ds) < 0.001 else ""
    print(f"  {d:>6.3f} | {P:>7.4f} | {R:>7.4f} | {S:>7.4f}{marker}")

print(f"\n{'='*60}")
print("【導出チェーン】")
print(f"  GER係数 (a=0.95, b=0.5, r=0.1, φ=1.618)")
print(f"    ↓ 不動点解析")
print(f"  G*=19φr, E*=log(1+19φr)")
print(f"    ↓ ヤコビアン")
print(f"  λ₁=0.95, λ₂=0.5")
print(f"    ↓ α=1-λ₁, β=φ×r")
print(f"  α=0.05, β=0.1618")
print(f"    ↓ δ*=β×ln(1+β/α)")
print(f"  δ* = 0.2336  （1/φ³=0.2361 の 1% 近似）")
print(f"{'='*60}")
```
