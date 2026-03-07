"""
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
SUT Phase Diagram
Unified Emergence Test
Cosmos / Brain / Cell / SNS / Market
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.stats import entropy

PHI = (1 + np.sqrt(5)) / 2


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# IET
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def iet(X, Y, bins=30):

    joint, _, _ = np.histogram2d(X, Y, bins=bins)

    jp = joint + 1e-12
    jp = jp / jp.sum()

    xp = jp.sum(axis=1)
    yp = jp.sum(axis=0)

    HX = entropy(xp)
    HY = entropy(yp)
    HXY = entropy(jp.flatten())

    MI = max(0, HX + HY - HXY)

    P = MI / HXY if HXY > 0 else 0

    HXgY = max(0, HXY - HY)
    HYgX = max(0, HXY - HX)

    I_suzuki = P * (HXgY + HYgX)

    return P, I_suzuki


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# COSMOS
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def cosmos_data(n=4000):

    dm = np.random.normal(0,1,n)
    de = dm*0.7 + np.random.normal(0,0.6,n)

    return dm,de


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# BRAIN
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def brain_data(n=4000):

    t = np.linspace(0,20,n)

    x = np.sin(10*t) + np.random.normal(0,0.5,n)
    y = np.sin(10*t+0.2) + np.random.normal(0,0.5,n)

    return x,y


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# CELL
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def cell_data(n=4000):

    G = np.zeros(n)
    E = np.zeros(n)

    G[0]=1
    E[0]=1

    for i in range(1,n):

        G[i]=0.95*(G[i-1]+0.1*PHI)+np.random.normal(0,0.05)
        G[i]=max(G[i],1e-6)

        E[i]=0.5*(E[i-1]+np.log(1+G[i]))

    return G,E


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# SNS
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def sns_data(n=4000):

    post=np.random.poisson(5,n)
    like=post+np.random.normal(0,2,n)

    return post,like


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# MARKET
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def market_data(n=4000):

    price=np.cumsum(np.random.normal(0,1,n))
    volume=np.abs(np.random.normal(100,30,n))

    return price,volume


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# SUT PHASE
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def sut_phase_diagram():

    systems={

        "Cosmos": cosmos_data(),
        "Brain": brain_data(),
        "Cell": cell_data(),
        "SNS": sns_data(),
        "Market": market_data()

    }

    results={}

    for k,(x,y) in systems.items():

        P,I=iet(x,y)

        results[k]=(P,I)

    return results


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# PLOT
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def plot_phase():

    r=sut_phase_diagram()

    plt.figure(figsize=(7,7))

    for k,(x,y) in r.items():

        plt.scatter(x,y,s=200,label=k)

    plt.xlabel("Interaction Density P")
    plt.ylabel("Information Emergence I_suzuki")

    plt.title("SUT Phase Diagram")

    plt.legend()

    plt.grid()

    plt.show()


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# MAIN
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

if __name__=="__main__":

    r=sut_phase_diagram()

    for k,v in r.items():

        print(k,v)

    plot_phase()
