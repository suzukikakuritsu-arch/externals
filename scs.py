# ==========================================================
# SUZUKI COSMIC SIMULATOR
# 11D Projection → Dark Matter → Cosmic Web → CMB → GW
# ==========================================================

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from sklearn.neighbors import NearestNeighbors
from scipy.fft import fft, fftfreq

# ----------------------------------------------------------
# 基本定数
# ----------------------------------------------------------

phi = (1 + np.sqrt(5)) / 2

DIM_HIGH = 11
DIM_LOW = 3
N_PARTICLES = 3000
G = 1


# ----------------------------------------------------------
# 1 高次元宇宙生成 (11D)
# ----------------------------------------------------------

def generate_high_dimension_universe():

    return np.random.normal(0,1,(N_PARTICLES,DIM_HIGH))


# ----------------------------------------------------------
# 2 黄金比射影 (11D → 3D)
# ----------------------------------------------------------

def projection_matrix():

    return np.array([

    [1,phi,1/phi,phi**2,1,phi,1/phi,phi**2,1,phi,1/phi],

    [phi,1/phi,phi**2,1,phi,1/phi,phi**2,1,phi,1/phi,phi**2],

    [1/phi,phi**2,1,phi,1/phi,phi**2,1,phi,1/phi,phi**2,1]

    ])


def project_to_3D(points):

    P = projection_matrix()

    pts = points @ P.T

    return pts / np.linalg.norm(pts,axis=1)[:,None]


# ----------------------------------------------------------
# 3 重力ポテンシャル
# ----------------------------------------------------------

def gravitational_potential(points):

    center = np.array([0,0,0])

    dist = np.linalg.norm(points-center,axis=1)

    return -G/(dist+0.01)


# ----------------------------------------------------------
# 4 ダークマターN体近似
# ----------------------------------------------------------

def dark_matter_step(points, dt=0.01):

    velocity = np.zeros_like(points)

    for i in range(len(points)):

        diff = points - points[i]

        r = np.linalg.norm(diff,axis=1)+0.01

        force = np.sum(diff/(r[:,None]**3),axis=0)

        velocity[i] += G*force*dt

    points += velocity*dt

    return points


# ----------------------------------------------------------
# 5 Cosmic Web生成
# ----------------------------------------------------------

def cosmic_web(points):

    nbrs = NearestNeighbors(n_neighbors=3).fit(points)

    _, indices = nbrs.kneighbors(points)

    edges = []

    for i in range(len(points)):

        for j in indices[i]:

            edges.append((i,j))

    return edges


# ----------------------------------------------------------
# 6 CMB生成
# ----------------------------------------------------------

def generate_cmb(size=256):

    noise = np.random.normal(0,1,(size,size))

    kx = fftfreq(size)

    ky = fftfreq(size)

    KX,KY = np.meshgrid(kx,ky)

    spectrum = 1/(KX**2+KY**2+0.001)

    cmb = np.real(np.fft.ifft2(np.fft.fft2(noise)*spectrum))

    return cmb


# ----------------------------------------------------------
# 7 重力波シミュレーション
# ----------------------------------------------------------

def gravitational_wave():

    t = np.linspace(0,1,2000)

    freq = 40

    chirp = np.sin(2*np.pi*freq*t*(1+t))

    envelope = np.exp(3*t)

    return t, chirp*envelope


# ----------------------------------------------------------
# 宇宙生成
# ----------------------------------------------------------

points11 = generate_high_dimension_universe()

points3 = project_to_3D(points11)

potential = gravitational_potential(points3)


# ダークマター進化

for _ in range(5):

    points3 = dark_matter_step(points3)


# Cosmic Web

edges = cosmic_web(points3)


# ----------------------------------------------------------
# 可視化
# ----------------------------------------------------------

fig = plt.figure(figsize=(14,6))

ax = fig.add_subplot(121,projection='3d')

ax.scatter(
points3[:,0],
points3[:,1],
points3[:,2],
c=potential,
s=2
)

for i,j in edges:

    ax.plot(
    [points3[i,0],points3[j,0]],
    [points3[i,1],points3[j,1]],
    [points3[i,2],points3[j,2]],
    linewidth=0.2,
    alpha=0.3
    )

ax.set_title("Cosmic Web Simulation")


# CMB

cmb = generate_cmb()

ax2 = fig.add_subplot(122)

ax2.imshow(cmb)

ax2.set_title("Simulated CMB")

plt.show()


# ----------------------------------------------------------
# 重力波
# ----------------------------------------------------------

t,gw = gravitational_wave()

plt.figure()

plt.plot(t,gw)

plt.title("Gravitational Wave Signal")

plt.xlabel("time")

plt.ylabel("strain")

plt.show()


print("Simulation complete")
