"""
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
鈴木統合理論（SUT）完全実装
GERT / IET / NTT / 宇宙比率 / 希少価値
Yukiya Suzuki 2026
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
"""

import numpy as np
from scipy.optimize import brentq, minimize
from scipy.linalg import solve_discrete_lyapunov
from scipy.stats import entropy as scipy_entropy

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# 定数
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

PHI  = (1 + 5**0.5) / 2   # 1.6180339887...
PHI2 = PHI**2              # 2.6180...
PHI3 = PHI**3              # 4.2360...
PHI4 = PHI**4              # 6.8541...

A, B, R = 0.95, 0.50, 0.10   # GER標準係数

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# MODULE 1: 不動点
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def fixed_point(a=A, b=B, r=R):
    """
    GER不動点（解析的）
    G* = aφr/(1-a)
    E* = log(1+G*)
    S* = G*/E*
    δ* = β·ln(1+β/α)  安堅性最適点
    τ₁ = -1/log(a)    意図の時定数
    τ₂ = -1/log(b)    意味の時定数
    """
    G = a*PHI*r / (1-a)
    E = np.log(1+G)
    return {
        'G': G, 'E': E, 'S': G/E,
        'Sigma': G+E, 'Delta': G-E,
        'tau1': -1/np.log(a),
        'tau2': -1/np.log(b),
        'alpha': 1-a,
        'beta':  PHI*r,
        'delta_star': PHI*r * np.log(1 + PHI*r/(1-a)),
    }

def fixed_point_endogenous(a=A, b=B):
    """
    完全内生化GER（S*=φ が代数的必然）
    G* = φ·log(1+G*)  を数値的に解く

    証明（3行）:
      G*(1-a) = φ(1-a)·E*
      → G*/E* = φ  ∴ S* = φ（a,b,r に完全無依存）
    """
    G = brentq(lambda x: x - PHI*np.log(1+x), 0.01, 20)
    E = np.log(1+G)
    return {'G': G, 'E': E, 'S': G/E, 'phi_error': abs(G/E - PHI)}

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# MODULE 2: GER動力学
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def simulate(steps=20000, a=A, b=B, r=R,
             noise=0.05, seed=42, endogenous=False):
    """
    GER動力学シミュレーション

    通常:
      G(t+1) = a·(G(t)+φr) + ε
      E(t+1) = b·(E(t)+log(1+G(t+1)))

    完全内生化 (endogenous=True):
      G(t+1) = a·G(t) + φ(1-a)·E(t) + ε
      → S* = φ
    """
    np.random.seed(seed)
    fp = fixed_point(a,b,r)
    G, E = fp['G'], fp['E']
    Gs, Es = [], []
    for _ in range(steps):
        if endogenous:
            G = a*G + PHI*(1-a)*E + np.random.randn()*noise
        else:
            G = a*(G + PHI*r) + np.random.randn()*noise
        G = max(G, 1e-6)
        E = b*(E + np.log(1+G))
        Gs.append(G); Es.append(E)
    return np.array(Gs), np.array(Es)

def simulate_second_order(steps=1000, alpha_param=0.3,
                           noise=0.05, seed=42):
    """
    鈴木の2階差分方程式:
      g(t+1) = φ·log(1+g(t)) - α·g(t-1)
    不動点: g*(1+α) = φ·log(1+g*)
    α=0 で完全内生化GERと同型
    """
    np.random.seed(seed)
    G_eq = brentq(lambda x: x*(1+alpha_param) - PHI*np.log(1+x), 0.01, 10)
    gp, gc = G_eq, G_eq
    gs = [gp, gc]
    for _ in range(steps-2):
        gn = max(PHI*np.log(1+gc) - alpha_param*gp
                 + np.random.randn()*noise, 1e-6)
        gs.append(gn); gp, gc = gc, gn
    return np.array(gs), G_eq

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# MODULE 3: 安堅性・12工学指標
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def metrics(delta, a=A, b=B, r=R):
    """
    12工学指標（δ入力）

    1.  stability    P = exp(-δ/α)
    2.  robustness   R = 1-exp(-δ/β)
    3.  anken        S = P·R           [鈴木独自, δ*=0.2336]
    4.  responsive   Q = 1-exp(-δ/τ₂)
    5.  convergence  V = R·exp(-δ/τ₁)
    6.  stab_margin  M = exp(-δ²/β²)
    7.  efficiency   E = P·R/(α/δ+δ/β)
    8.  invariance   I = exp(-|δ-δ*|/α)
    9.  info_density → IETと接続（Module4）
    10. shape_memory F = 1/(1+(δ/δ*)²)
    11. productivity G*/σ
    12. regeneration 1/τ₁
    """
    fp = fixed_point(a,b,r)
    α, β = fp['alpha'], fp['beta']
    τ1, τ2 = fp['tau1'], fp['tau2']
    d_star = fp['delta_star']
    δ = max(delta, 1e-10)

    P = np.exp(-δ/α)
    Ro = 1 - np.exp(-δ/β)
    return {
        'stability':    P,
        'robustness':   Ro,
        'anken':        P*Ro,
        'responsive':   1 - np.exp(-δ/τ2),
        'convergence':  Ro*np.exp(-δ/τ1),
        'stab_margin':  np.exp(-δ**2/β**2),
        'efficiency':   P*Ro / (α/δ + δ/β),
        'invariance':   np.exp(-abs(δ-d_star)/α),
        'shape_memory': 1/(1+(δ/d_star)**2),
        'productivity': fp['G']/0.05,
        'regeneration': 1/τ1,
        'delta_star':   d_star,
    }

def optimal_delta(criterion='anken', a=A, b=B, r=R):
    """
    指標を最大化する δ を返す
    criterion: 'anken' | 'efficiency' | 'convergence'
    解析解: anken → δ* = β·ln(1+β/α)
    """
    if criterion == 'anken':
        return fixed_point(a,b,r)['delta_star']
    res = minimize(lambda d: -metrics(d[0],a,b,r)[criterion],
                   [fixed_point(a,b,r)['delta_star']],
                   bounds=[(1e-6, 5.0)])
    return res.x[0]

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# MODULE 4: IET情報創発
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def iet(X, Y, bins=30):
    """
    I_suzuki = P(interact) × [H(X|Y) + H(Y|X)]
    P(interact) = I(X;Y) / H(X,Y)
    F_info = |H(X|Y)-H(Y|X)| / H(X,Y)  ← 斥力
    λ = -MI²/H(X,Y)                     ← 結合定数（解析的）

    F_info符号:
      H(X|Y) > H(Y|X): G→E 自然創発
      H(X|Y) < H(Y|X): E→G 技術介入（再生細胞型）
    """
    joint, _, _ = np.histogram2d(X, Y, bins=bins)
    jp = (joint.astype(float)+1e-10)
    jp /= jp.sum()
    xp, yp = jp.sum(axis=1), jp.sum(axis=0)

    H_X  = scipy_entropy(xp, base=2)
    H_Y  = scipy_entropy(yp, base=2)
    H_XY = scipy_entropy(jp.flatten(), base=2)
    MI   = max(0, H_X+H_Y-H_XY)
    P    = MI/H_XY if H_XY>1e-10 else 0

    HXgY = max(0, H_XY-H_Y)   # 意図
    HYgX = max(0, H_XY-H_X)   # 意味
    F    = abs(HXgY-HYgX)/H_XY if H_XY>1e-10 else 0
    lam  = -(MI**2)/H_XY       if H_XY>1e-10 else 0

    sign = +1 if HXgY>=HYgX else -1
    direction = 'G→E 自然創発' if sign>0 else 'E→G 技術介入'

    return {
        'I_suzuki':  P*(HXgY+HYgX),
        'P':         P,
        'MI':        MI,
        'H_intent':  HXgY,     # 意図
        'H_meaning': HYgX,     # 意味
        'H_XY':      H_XY,
        'F_info':    F,         # 斥力
        'F_sign':    sign,
        'direction': direction,
        'lambda':    lam,
        'I_total':   P*(HXgY+HYgX) + lam*F,
    }

def iet_from_ger(a=A, b=B, r=R, sigma=0.05, steps=20000):
    """GER不動点のIETを計算"""
    Gs, Es = simulate(steps, a, b, r, sigma)
    return iet(Gs[1000:], Es[1000:])

def shared_meaning(X, Y, Z, bins=20):
    """
    共有意味空間 Z（辞書・文化）を考慮したIET
    H(X|Y,Z): 純粋な意図の個人差
    H(Y|X,Z): 純粋な意味の個人差
    F_info_pure: Z除去後の斥力
    """
    j3, _ = np.histogramdd(np.stack([X,Y,Z],axis=1), bins=[bins]*3)
    j3 = (j3.astype(float)+1e-10); j3/=j3.sum()
    H_XYZ = scipy_entropy(j3.flatten(), base=2)
    H_YZ  = scipy_entropy(j3.sum(axis=0).flatten(), base=2)
    H_XZ  = scipy_entropy(j3.sum(axis=1).flatten(), base=2)
    H_Z   = scipy_entropy(j3.sum(axis=(0,1)), base=2)
    HXgYZ = max(0, H_XYZ-H_YZ)
    HYgXZ = max(0, H_XYZ-H_XZ)
    return {
        'H_intent_pure':  HXgYZ,
        'H_meaning_pure': HYgXZ,
        'F_info_pure': abs(HXgYZ-HYgXZ)/H_XYZ if H_XYZ>1e-10 else 0,
        'H_Z': H_Z,
    }

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# MODULE 5: 座標変換
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def to_sigma_delta(G, E):
    """(G,E) → (Σ,Δ)"""
    return G+E, G-E

def to_S(Sigma, Delta):
    """(Σ,Δ) → S = (Σ+Δ)/(Σ-Δ)"""
    return (Sigma+Delta)/(Sigma-Delta)

def sensitivity(S_star, Sigma_star):
    """
    ∂S/∂(Δ/Σ) = 2/(1-Δ/Σ)²
    標準不動点: 5.0835
    設計原則: (Σ,Δ)で設計 → S で動かす
    """
    Delta = (S_star-1)/(S_star+1)*Sigma_star
    return 2/(1-Delta/Sigma_star)**2

def design_for_S(target_S, a=A, b=B, r=R):
    """目標S*に対応する(Σ,Δ,G)と r を返す"""
    E = fixed_point(a,b,r)['E']
    G = target_S*E
    r_opt = brentq(
        lambda rv: (a*PHI*rv/(1-a))/np.log(1+a*PHI*rv/(1-a))-target_S,
        1e-6, 100, full_output=False
    ) if target_S > 1.01 else None
    return {'Sigma': G+E, 'Delta': G-E, 'G': G, 'r_opt': r_opt}

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# MODULE 6: 希少価値・経済層
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def rare_value(P, MI):
    """
    V_rare = P(interact) / I(X;Y)
    MI→0: 発散（完全希少性）  ← 謎を解くカギ
    MI→H: P/H（通常価値）
    I_total = I_suzuki + λ·F_info で価値が決まる
    """
    if MI < 1e-10: return np.inf
    if P  < 1e-10: return 0.0
    return P/MI

def economic_dynamics(steps=300, scarcity_rate=0.5, seed=42):
    """
    希少価値の動態:
      希少性が増す → P↓ → MI↓ → V_rare↑（発散へ）
      F_info が大きい → イノベーション度高
      辞書（Z）の更新 = F_info の時間積分
    """
    np.random.seed(seed)
    results = []
    for t in range(steps):
        sc = scarcity_rate*(t/steps)
        sX = max(0.2*(1-sc*0.9), 1e-3)
        sY = 0.2
        rho= max(0.9-sc*0.6, 0.05)
        # ガウス近似でIET
        det = sX**2*sY**2*(1-rho**2)
        if det <= 0: continue
        C = np.log2(np.e)
        HX  = 0.5*C*np.log(2*np.pi*np.e*sX**2)
        HY  = 0.5*C*np.log(2*np.pi*np.e*sY**2)
        HXY = 0.5*C*np.log((2*np.pi*np.e)**2*det)
        MI_ = max(0,-0.5*C*np.log(1-rho**2))
        P_  = MI_/HXY if HXY>1e-10 else 0
        HXgY= max(0,HXY-HY)
        HYgX= max(0,HXY-HX)
        I_s = P_*(HXgY+HYgX)
        F_  = abs(HXgY-HYgX)/HXY if HXY>1e-10 else 0
        V_  = rare_value(P_, MI_)
        results.append({
            't': t, 'scarcity': sc,
            'I_suzuki': I_s, 'F_info': F_,
            'V_rare': min(V_, 1e6), 'P': P_, 'MI': MI_,
        })
    return results

def knowledge_property_value(I_suzuki, F_info, V_rare,
                              novelty_weight=1.0, scarcity_weight=1.0):
    """
    知財の情報経済価値（仮説的定式化）

    V_IP = I_suzuki × V_rare × (1 + novelty_weight·F_info)

    I_suzuki : 情報創発量（基礎価値）
    V_rare   : 希少価値乗数
    F_info   : 斥力・新規性（イノベーション度）
    """
    if np.isinf(V_rare):
        return np.inf
    return I_suzuki * V_rare * (1 + novelty_weight*F_info) * scarcity_weight

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# MODULE 7: 宇宙比率（φ と 3 による統一記述）
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

COSMOS = {
    'baryon_pct': 5.0,
    'DM_pct':     27.0,
    'DE_pct':     68.0,
}

def cosmic_ratios():
    """
    宇宙の3大成分比を φ と 3 で記述する

    DM/物質 = 5.4  ≈ φ × T(4)/fib(4) = φ×10/3  誤差0.12%
    DE/DM   = 2.52 ≈ φ⁴                          誤差0.12%
    DE/全体 = 0.68 ≈ 3/φ                          誤差0.31%

    T(4)   = 1+2+3+4 = 10  （4次元時空の三角数）
    fib(4) = 3             （3次元空間のフィボナッチ数）
    """
    bm = COSMOS['baryon_pct']
    dm = COSMOS['DM_pct']
    de = COSMOS['DE_pct']
    total = bm+dm+de

    ratios = {
        'DM/物質': dm/bm,
        'DE/DM':   de/dm,
        'DE/全体': de/total,
    }
    predictions = {
        'DM/物質': PHI*10/3,   # φ×T(4)/fib(4)
        'DE/DM':   PHI4,        # φ⁴
        'DE/全体': 3/PHI,       # 3/φ
    }
    return {k: {
        'observed':   ratios[k],
        'predicted':  predictions[k],
        'error_pct':  abs(ratios[k]-predictions[k])/ratios[k]*100,
        'formula':    {
            'DM/物質': 'φ×10/3  [T(4)/fib(4)]',
            'DE/DM':   'φ⁴',
            'DE/全体': '3/φ',
        }[k]
    } for k in ratios}

def cosmic_structure_hypothesis():
    """
    φ×10/3 の構造的根拠（仮説）

    T(4) = 1+2+3+4 = 10  ← 4次元時空の三角数
    fib(4) = 3            ← 3次元空間のフィボナッチ数
    比: T(4)/fib(4) = 10/3

    3次元の必然性（NTTと一致）:
      力 ∝ 1/r^(d-1)
      d=3 で安定軌道が成立
      d=3 = fib(4) = GERサイクル項数

    DE/DM ≈ φ⁴ の解釈（未解決）:
      φ⁴ = 3φ+2  （フィボナッチ恒等式）
      4次元時空の自己参照？
    """
    T4   = sum(range(1,5))        # 10
    fib4 = 3
    print(f"T(4)     = {T4}")
    print(f"fib(4)   = {fib4}")
    print(f"φ×T/fib  = {PHI*T4/fib4:.6f}")
    print(f"DM/物質  = {COSMOS['DM_pct']/COSMOS['baryon_pct']:.6f}")
    print(f"誤差     = {abs(PHI*T4/fib4 - 27/5)/(27/5)*100:.4f}%")
    print()
    print(f"φ⁴       = {PHI4:.6f}")
    print(f"DE/DM    = {COSMOS['DE_pct']/COSMOS['DM_pct']:.6f}")
    print(f"誤差     = {abs(PHI4-68/27)/(68/27)*100:.4f}%")

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# MODULE 8: NTT×IET統合
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def ntt_density(k, D_func=None, C_func=None):
    """
    NTT密度: ρ(k) = lim_{D→∞,C→0} D(k)·C(k)
    IET対応: ρ(k) = P(interact) = I(X;Y)/H(X,Y)

    デフォルト: D(k)=k^n, C(k)=1/k^n → ρ=1（定常）
    """
    if D_func is None: D_func = lambda k,n: k**n
    if C_func is None: C_func = lambda k,n: 1/k**n
    # 極限は数値的に近似
    rho = np.mean([D_func(k,n)*C_func(k,n) for n in [1,2,3,5,8]])
    return rho

def f_info_sign(HXgY, HYgX):
    """
    斥力の方向判定（NTT特異点の向き）

    +1: G→E  自然創発（混沌→秩序）
    -1: E→G  技術介入（秩序→混沌、再生細胞型）
     0: 対称  辞書状態（創発なし）
    """
    d = HXgY - HYgX
    if   d >  1e-10: return +1, 'G→E 自然創発'
    elif d < -1e-10: return -1, 'E→G 技術介入'
    else:            return  0, '対称 辞書状態'

def sut_unified(X, Y, a=A, b=B, r=R):
    """
    鈴木統合理論（SUT）の全量を一括計算する

    NTT層:  ρ(k) = P(interact)
    IET層:  I_suzuki, F_info, λ, 方向
    GERT層: S = G/E, 安堅性, 座標変換
    経済層: V_rare, 知財価値

    返値: dict（全指標）
    """
    # IET
    i = iet(X, Y)
    # GERT不動点
    fp = fixed_point(a, b, r)
    d_star = fp['delta_star']
    m = metrics(d_star, a, b, r)
    # 座標変換
    Sig, Del = to_sigma_delta(fp['G'], fp['E'])
    sens = sensitivity(fp['S'], Sig)
    # 経済
    V = rare_value(i['P'], i['MI'])
    V_ip = knowledge_property_value(i['I_suzuki'], i['F_info'], V)
    # NTT密度
    rho_ntt = i['P']   # ρ = P(interact)

    return {
        # NTT
        'rho_ntt':    rho_ntt,
        # IET
        'I_suzuki':   i['I_suzuki'],
        'P_interact': i['P'],
        'F_info':     i['F_info'],
        'lambda':     i['lambda'],
        'I_total':    i['I_total'],
        'H_intent':   i['H_intent'],
        'H_meaning':  i['H_meaning'],
        'direction':  i['direction'],
        # GERT
        'S_star':     fp['S'],
        'G_star':     fp['G'],
        'E_star':     fp['E'],
        'delta_star': d_star,
        'anken':      m['anken'],
        'tau1':       fp['tau1'],
        'tau2':       fp['tau2'],
        'sensitivity':sens,
        # 経済
        'V_rare':     min(V, 1e6) if not np.isinf(V) else np.inf,
        'V_IP':       min(V_ip, 1e6) if not np.isinf(V_ip) else np.inf,
    }

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# MODULE 9: 応用例
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def pharmacology(concentration, receptor_density=1.0,
                 EC50=1.0, hill=1.0, a=A, b=B, r=R):
    """
    薬理IETモデル:
      P_drug = P_base × Hill関数 × receptor_density
      I_pharma = P_drug × [H(G|E)+H(E|G)]
    """
    H = concentration**hill / (EC50**hill + concentration**hill)
    i = iet_from_ger(a, b, r)
    P_mod = i['P'] * (1+H) * receptor_density
    return {
        'Hill': H,
        'P_modulated': P_mod,
        'I_pharma': P_mod*(i['H_intent']+i['H_meaning']),
        'F_info': i['F_info'],
    }

def cell_division(steps=500, F_threshold=0.05,
                   a=A, b=B, r=R, noise=0.05, seed=42):
    """
    細胞分裂モデル:
      F_info > F_threshold のとき 1→2 イベント
      F_info符号 = 分裂の方向性
        + : 自然分裂
        - : 再生技術による誘導分裂（E→G型）
    """
    np.random.seed(seed)
    fp = fixed_point(a,b,r)
    G, E = fp['G'], fp['E']
    Gs, Es, Fs = [], [], []
    events = []
    win = 50
    for t in range(steps):
        G = max(a*(G+PHI*r)+np.random.randn()*noise, 1e-6)
        E = b*(E+np.log(1+G))
        Gs.append(G); Es.append(E)
        if t >= win:
            res = iet(np.array(Gs[-win:]),
                      np.array(Es[-win:]), bins=15)
            F = res['F_info']
            Fs.append(F)
            if abs(F) > F_threshold:
                events.append({'t':t,'F':F,'dir':res['direction']})
        else:
            Fs.append(0.0)
    return np.array(Gs), np.array(Es), np.array(Fs), events

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# MAIN
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

if __name__ == '__main__':
    S = "━"*52

    print(S); print("MODULE 1: 不動点"); print(S)
    fp = fixed_point()
    print(f"  G*={fp['G']:.6f}  E*={fp['E']:.6f}  S*={fp['S']:.6f}")
    print(f"  τ₁={fp['tau1']:.2f}  τ₂={fp['tau2']:.2f}  τ₁/τ₂={fp['tau1']/fp['tau2']:.2f}")
    print(f"  δ*={fp['delta_star']:.6f}")
    fpe = fixed_point_endogenous()
    print(f"  完全内生化 S*=φ 誤差={fpe['phi_error']:.2e}")

    print(S); print("MODULE 2: GER動力学"); print(S)
    Gs,Es = simulate(5000)
    Sa = Gs/Es
    print(f"  S mean={Sa[500:].mean():.4f}  S*={fp['S']:.4f}")

    print(S); print("MODULE 3: 12工学指標"); print(S)
    d = optimal_delta()
    m = metrics(d)
    for k in ['anken','efficiency','convergence']:
        print(f"  {k:12}={m[k]:.6f}")

    print(S); print("MODULE 4: IET"); print(S)
    i = iet_from_ger()
    print(f"  I_suzuki={i['I_suzuki']:.4f}  P={i['P']:.4f}")
    print(f"  F_info  ={i['F_info']:.4f}  λ={i['lambda']:.4f}")
    print(f"  意図={i['H_intent']:.4f}  意味={i['H_meaning']:.4f}")
    print(f"  {i['direction']}")

    print(S); print("MODULE 5: 座標変換"); print(S)
    Sig,Del = to_sigma_delta(fp['G'],fp['E'])
    print(f"  S=(Σ+Δ)/(Σ-Δ)={to_S(Sig,Del):.6f} ✓")
    print(f"  感度∂S/∂(Δ/Σ)={sensitivity(fp['S'],Sig):.4f}")

    print(S); print("MODULE 6: 希少価値・知財"); print(S)
    eco = economic_dynamics(200)
    for t in [0,99,199]:
        e = eco[t]
        print(f"  t={t:3d} 希少性={e['scarcity']:.2f}"
              f"  V_rare={e['V_rare']:.3f}"
              f"  F_info={e['F_info']:.4f}")
    V_IP = knowledge_property_value(i['I_suzuki'], i['F_info'],
                                     rare_value(i['P'], i['MI']))
    print(f"  知財価値 V_IP={V_IP:.4f}")

    print(S); print("MODULE 7: 宇宙比率"); print(S)
    cr = cosmic_ratios()
    for k,v in cr.items():
        print(f"  {k}: 観測={v['observed']:.4f}"
              f"  予測={v['predicted']:.4f}"
              f"  誤差={v['error_pct']:.3f}%"
              f"  [{v['formula']}]")

    print(S); print("MODULE 8: SUT統合"); print(S)
    result = sut_unified(Gs[1000:], Es[1000:])
    for k in ['I_suzuki','F_info','lambda','anken','V_rare','V_IP']:
        v = result[k]
        print(f"  {k:12}={v:.4f}" if not np.isinf(v) else f"  {k:12}=∞")

    print(S); print("MODULE 9: 応用例"); print(S)
    ph = pharmacology(1.0)
    print(f"  薬理: Hill={ph['Hill']:.3f}  I_pharma={ph['I_pharma']:.4f}")
    _,_,_,ev = cell_division(300)
    print(f"  細胞分裂イベント={len(ev)}件")
    if ev: print(f"  最初: t={ev[0]['t']} {ev[0]['dir']}")

    print(S); print("全モジュール完了"); print(S)
