"""
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
SUT Industrial IP Protection & Engineering Value Module
全産業知財保護 + 工学指標価値スコア
Yukiya Suzuki 2026
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
"""

import hashlib
import numpy as np
from scipy.optimize import minimize
from scipy.stats import entropy

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# CONSTANTS
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

PHI = (1 + np.sqrt(5)) / 2

A, B, R = 0.95, 0.5, 0.1  # GER coefficients

ENGINEERING_INDICATORS = [
    "stability", "robustness", "anken", "responsive", "convergence",
    "stab_margin", "efficiency", "invariance", "info_density",
    "shape_memory", "productivity", "regeneration"
]

# 対象産業リスト
INDUSTRIES = [
    "drone", "AI", "autonomous_vehicle", "robotics", "regenerative_medicine",
    "drug_discovery", "medical_device", "SNS", "platform", "API", "SaaS", "logistics"
]

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# MODULE 1: 工学指標計算
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def fixed_point(a=A, b=B, r=R):
    G = a*PHI*r / (1-a)
    E = np.log(1+G)
    S = G/E
    tau1 = -1/np.log(a)
    tau2 = -1/np.log(b)
    alpha, beta = 1-a, PHI*r
    delta_star = beta * np.log(1+beta/alpha)
    return dict(G=G, E=E, S=S, tau1=tau1, tau2=tau2,
                alpha=alpha, beta=beta, delta_star=delta_star)

def metrics(delta, a=A, b=B, r=R):
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
    if criterion == 'anken':
        return fixed_point(a,b,r)['delta_star']
    res = minimize(lambda d: -metrics(d[0],a,b,r)[criterion],
                   [fixed_point(a,b,r)['delta_star']],
                   bounds=[(1e-6,5.0)])
    return res.x[0]

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# MODULE 2: 情報創発理論
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def iet(X,Y,bins=30):
    joint,_x,_y = np.histogram2d(X,Y,bins=bins)
    jp = joint.astype(float)+1e-12
    jp /= jp.sum()
    xp, yp = jp.sum(axis=1), jp.sum(axis=0)
    HX = entropy(xp)
    HY = entropy(yp)
    HXY = entropy(jp.flatten())
    MI = max(0,HX+HY-HXY)
    P = MI/HXY if HXY>0 else 0
    HXgY = max(0,HXY-HY)
    HYgX = max(0,HXY-HX)
    F = abs(HXgY-HYgX)/HXY if HXY>0 else 0
    I_suzuki = P*(HXgY+HYgX)
    direction = "G→E" if HXgY>=HYgX else "E→G"
    return dict(I_suzuki=I_suzuki, MI=MI, P=P, H_intent=HXgY,
                H_meaning=HYgX, F_info=F, direction=direction)

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# MODULE 3: 知財保護コード
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

class IndustrialIP:
    def __init__(self, industry, secret_key):
        self.industry = industry
        self.secret_key = secret_key
        self.registry = {}

    def encrypt_ip(self, ip_content):
        """
        産業知財をハッシュ化＋鍵で保護
        """
        m = hashlib.sha256()
        m.update((ip_content + self.secret_key).encode('utf-8'))
        return m.hexdigest()

    def register_ip(self, ip_name, ip_content):
        self.registry[ip_name] = self.encrypt_ip(ip_content)

    def validate_access(self, ip_name, ip_content):
        expected = self.registry.get(ip_name)
        if not expected:
            return False
        return expected == self.encrypt_ip(ip_content)

    def get_ip_summary(self, ip_name):
        return f"[PROTECTED] Industrial IP: {ip_name} in {self.industry}"

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# MODULE 4: 産業知財価値スコア
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def knowledge_property_value(I_suzuki, F_info, novelty_weight=1.0, scarcity_weight=1.0):
    """
    情報創発量＋斥力で知財価値をスコア化
    """
    return I_suzuki * (1 + novelty_weight*F_info) * scarcity_weight

def engineering_value_score(delta=None):
    """
    工学指標を総合スコア化
    """
    if delta is None:
        delta = optimal_delta()
    m = metrics(delta)
    return np.mean([m[ind] for ind in ENGINEERING_INDICATORS if ind in m])

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# MODULE 5: 全産業IP管理
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

class GlobalIPRegistry:
    def __init__(self, secret_root="root_secret_2026"):
        self.secret_root = secret_root
        self.industries = {}
        for ind in INDUSTRIES:
            self.industries[ind] = IndustrialIP(ind, secret_root + "_" + ind)

    def register(self, industry, ip_name, ip_content):
        self.industries[industry].register_ip(ip_name, ip_content)

    def validate(self, industry, ip_name, ip_content):
        return self.industries[industry].validate_access(ip_name, ip_content)

    def summarize(self, industry, ip_name):
        return self.industries[industry].get_ip_summary(ip_name)

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# MODULE 6: デモ
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

if __name__ == "__main__":
    # SUT工学価値
    ev_score = engineering_value_score()
    print(f"SUT Engineering Value Score: {ev_score:.4f}")

    # IET情報創発例
    X, Y = np.random.randn(5000), np.random.randn(5000)
    i = iet(X,Y)
    print(f"IET Emergence: {i['I_suzuki']:.4f}, F_info={i['F_info']:.4f}")

    # 全産業知財保護
    registry = GlobalIPRegistry()
    registry.register("AI", "neural_algo", "def neural_model(...): pass")
    access_ok = registry.validate("AI", "neural_algo", "def neural_model(...): pass")
    print(f"AI IP access valid: {access_ok}")
    print(registry.summarize("AI", "neural_algo"))
