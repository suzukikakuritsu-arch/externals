# ==========================================================
# Universal Emergence Simulator
# Suzuki Information Emergence Model
# Universe → Life → Molecules → AI
# ==========================================================

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D

# ----------------------------
# 基本定数
# ----------------------------

PHI = (1 + np.sqrt(5)) / 2
DIM_HIGH = 11
DIM_LOW = 3
np.random.seed(0)

# ----------------------------
# 1 高次元宇宙格子
# ----------------------------

def generate_universe(n=600):

    return np.random.normal(0,1,(n,DIM_HIGH))


# ----------------------------
# 2 準結晶射影
# ----------------------------

def quasicrystal_projection(points):

    M = np.random.normal(0,1,(DIM_HIGH,DIM_LOW))

    M[0,0] *= PHI
    M[1,1] *= PHI

    return points @ M


# ----------------------------
# 3 情報相互作用
# ----------------------------

def information_interaction(points):

    N=len(points)
    J=np.zeros((N,N))

    for i in range(N):
        for j in range(i+1,N):

            d=np.linalg.norm(points[i]-points[j])

            strength=np.exp(-d)

            J[i,j]=strength
            J[j,i]=strength

    return J


# ----------------------------
# 4 創発ダイナミクス
# ----------------------------

def emergence_dynamics(points,J,steps=80):

    X=points.copy()

    for t in range(steps):

        influence=J@X

        X = X + 0.02*(influence - X)

    return X


# ----------------------------
# 5 創薬的クラスタ検出
# ----------------------------

def cluster_detection(points):

    clusters=[]

    for p in points:

        if np.linalg.norm(p)<2:

            clusters.append(p)

    return np.array(clusters)


# ----------------------------
# 6 情報エントロピー
# ----------------------------

def information_entropy(J):

    p=J.flatten()
    p=p/np.sum(p)

    H=-np.sum(p*np.log(p+1e-12))

    return H


# ----------------------------
# 7 可視化
# ----------------------------

def visualize(points,clusters):

    fig=plt.figure()
    ax=fig.add_subplot(111,projection='3d')

    ax.scatter(points[:,0],points[:,1],points[:,2],s=3)

    if len(clusters)>0:

        ax.scatter(
            clusters[:,0],
            clusters[:,1],
            clusters[:,2],
            s=20
        )

    plt.title("Universal Emergence Structure")
    plt.show()


# ==========================================================
# 実行
# ==========================================================

universe=generate_universe()

projection=quasicrystal_projection(universe)

J=information_interaction(projection)

emergence=emergence_dynamics(projection,J)

clusters=cluster_detection(emergence)

entropy=information_entropy(J)

print("Golden ratio:",PHI)
print("Information entropy:",entropy)
print("Emergent clusters:",len(clusters))

visualize(emergence,clusters)
