# =====================================================
# Cosmic Filament Simulator
# 11D → φ Quasicrystal → Cosmic Web
# =====================================================

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D

# -----------------------------
# 定数
# -----------------------------

PHI = (1 + np.sqrt(5)) / 2
DIM_HIGH = 11
DIM_LOW = 3

np.random.seed(1)

# ----------------------------------------
# 1 高次元宇宙空間
# ----------------------------------------

def generate_universe(n=1000):

    return np.random.normal(0,1,(n,DIM_HIGH))


# ----------------------------------------
# 2 φ準結晶射影
# ----------------------------------------

def phi_projection(points):

    P = np.random.normal(0,1,(DIM_HIGH,DIM_LOW))

    for i in range(3):
        P[i,i] *= PHI

    return points @ P


# ----------------------------------------
# 3 重力相互作用
# ----------------------------------------

def gravity_step(points,dt=0.01):

    N=len(points)

    new_points = points.copy()

    for i in range(N):

        force=np.zeros(3)

        for j in range(N):

            if i==j:
                continue

            r=points[j]-points[i]

            d=np.linalg.norm(r)+1e-4

            force += r/(d**3)

        new_points[i]+=dt*force

    return new_points


# ----------------------------------------
# 4 フィラメント進化
# ----------------------------------------

def evolve(points,steps=40):

    X=points.copy()

    for t in range(steps):

        X=gravity_step(X)

    return X


# ----------------------------------------
# 5 フィラメント可視化
# ----------------------------------------

def visualize(points):

    fig=plt.figure(figsize=(7,6))
    ax=fig.add_subplot(111,projection='3d')

    ax.scatter(
        points[:,0],
        points[:,1],
        points[:,2],
        s=2
    )

    ax.set_title("Cosmic Filament Structure")

    plt.show()


# =====================================================
# 実行
# =====================================================

universe = generate_universe()

projection = phi_projection(universe)

filaments = evolve(projection)

print("φ =",PHI)
print("particle count =",len(filaments))

visualize(filaments)
