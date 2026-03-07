# ============================================================
# Nonlinear GER Chaos Economic Model - Full Research Template
# ============================================================

import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import minimize
from scipy.linalg import eigvals
from scipy.stats import jarque_bera
from statsmodels.tsa.stattools import adfuller, acf
import statsmodels.api as sm

print("==============================================")
print(" Nonlinear GER Chaos Economic Model Framework ")
print("==============================================")

# ============================================================
# 1 DATA
# ============================================================

years = np.arange(2000,2024)

gdp = np.array([
3986.76,4002.15,4003.83,4065.29,4154.16,4229.1,4287.14,
4350.76,4297.49,4052.83,4218.91,4219.91,4277.93,
4363.7,4376.63,4444.93,4478.44,4553.47,4582.76,
4564.33,4375.04,4487.02,4529.85,4605.91
])

growth = np.diff(np.log(gdp))

print("Observations:",len(growth))
print("Mean:",growth.mean())
print("Std:",growth.std())

# ============================================================
# 2 STATIONARITY TEST
# ============================================================

print("\n--- ADF TEST ---")

adf = adfuller(growth)

print("ADF statistic:",adf[0])
print("p-value:",adf[1])

# ============================================================
# 3 NONLINEAR GER MODEL
# ============================================================

def ger_nonlinear_predict(params,data):

    phi,alpha = params

    pred = []

    for t in range(1,len(data)-1):

        val = phi*np.log(1+data[t]) - alpha*data[t-1]

        pred.append(val)

    return np.array(pred)

def ger_loss(params,data):

    pred = ger_nonlinear_predict(params,data)

    true = data[2:]

    return np.mean((pred-true)**2)

# ============================================================
# 4 PARAMETER ESTIMATION
# ============================================================

res = minimize(
    ger_loss,
    x0=[1.0,0.3],
    args=(growth,),
    bounds=[(0,3),(0,2)]
)

phi,alpha = res.x

print("\n--- GER PARAMETERS ---")
print("phi =",phi)
print("alpha =",alpha)

# ============================================================
# 5 MODEL FIT
# ============================================================

pred = ger_nonlinear_predict(res.x,growth)

true = growth[2:]

resid = true - pred

mse = np.mean(resid**2)

rmse = np.sqrt(mse)

print("\nRMSE:",rmse)

# ============================================================
# 6 RESIDUAL DIAGNOSTICS
# ============================================================

print("\n--- RESIDUAL TEST ---")

jb = jarque_bera(resid)

print("Jarque-Bera:",jb)

acf_vals = acf(resid,nlags=8)

# ============================================================
# 7 DYNAMICAL SYSTEM ANALYSIS
# ============================================================

# Jacobian approximation near equilibrium
def jacobian(phi,alpha,g):

    dg = phi/(1+g)

    J = np.array([
        [dg, -alpha],
        [1, 0]
    ])

    return J

g_star = np.mean(growth)

J = jacobian(phi,alpha,g_star)

eig = eigvals(J)

lyapunov = np.log(np.max(np.abs(eig)))

print("\n--- DYNAMICS ---")

print("Eigenvalues:",eig)
print("Lyapunov approx:",lyapunov)

if lyapunov < 0:
    print("Stable dynamics")

elif lyapunov == 0:
    print("Periodic")

else:
    print("Chaotic tendency")

# ============================================================
# 8 PHASE SPACE
# ============================================================

x = growth[:-1]
y = growth[1:]

# ============================================================
# 9 FORECAST
# ============================================================

g_t = growth[-1]
g_tm1 = growth[-2]

forecast = phi*np.log(1+g_t) - alpha*g_tm1

print("\nNext growth forecast:",forecast)

# ============================================================
# 10 BOOTSTRAP INTERVAL
# ============================================================

sim = []

for i in range(1000):

    e = np.random.choice(resid)

    sim.append(forecast + e)

sim = np.array(sim)

ci = np.percentile(sim,[5,95])

print("90% forecast interval:",ci)

# ============================================================
# 11 CHAOS SIMULATION
# ============================================================

sim_dyn = []

g1 = growth[-2]
g2 = growth[-1]

for i in range(200):

    g3 = phi*np.log(1+g2) - alpha*g1

    sim_dyn.append(g3)

    g1,g2 = g2,g3

# ============================================================
# 12 VISUALIZATION
# ============================================================

years_vis = years[2:]

plt.figure(figsize=(14,10))

plt.subplot(231)
plt.plot(years_vis,true,label="Real")
plt.plot(years_vis,pred,label="GER nonlinear")
plt.legend()
plt.title("Model Fit")

plt.subplot(232)
plt.plot(years_vis,resid)
plt.axhline(0,color='black')
plt.title("Residuals")

plt.subplot(233)
plt.bar(range(len(acf_vals)),acf_vals)
plt.title("Residual ACF")

plt.subplot(234)
plt.hist(resid,bins=10)
plt.title("Residual distribution")

plt.subplot(235)
plt.scatter(x,y)
plt.title("Phase space")

plt.subplot(236)
plt.plot(sim_dyn)
plt.title("Nonlinear dynamics simulation")

plt.tight_layout()

plt.savefig("GER_nonlinear_chaos_model.png",dpi=200)

plt.close()

print("\nFigure saved: GER_nonlinear_chaos_model.png")

print("\n==============================================")
print(" Nonlinear GER Analysis Complete ")
print("==============================================")
