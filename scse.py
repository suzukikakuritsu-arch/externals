# ==========================================================
# SUZUKI COSMIC SIMULATOR EXTENDED
# High-D Universe → Dark Matter → Cosmic Web → CMB → GW
# ==========================================================

import numpy as np
import matplotlib.pyplot as plt
from sklearn.neighbors import NearestNeighbors
from scipy.fft import fft2, ifft2, fftfreq

# ----------------------------------------------------------
# 定数
# ----------------------------------------------------------

PHI = (1 + np.sqrt(5)) / 2

DIM_HIGH = 11
DIM_LOW = 3

N_PARTICLES = 5000
TIME_STEPS = 15

G = 1.0
DT = 0.01

# ----------------------------------------------------------
# 1 高次元宇宙
# ----------------------------------------------------------

def generate_high_dimension_universe():

    return np.random.normal(0,1,(N_PARTICLES,DIM_HIGH))


# ----------------------------------------------------------
# 2 黄金比射影
# ----------------------------------------------------------

def projection_matrix():

    return np.array([

        [1,PHI,1/PHI,PHI**2,1,PHI,1/PHI,PHI**2,1,PHI,1/PHI],

        [PHI,1/PHI,PHI**2,1,PHI,1/PHI,PHI**2,1,PHI,1/PHI,PHI**2],

        [1/PHI,PHI**2,1,PHI,1/PHI,PHI**2,1,PHI,1/PHI,PHI**2,1]

    ])


def project_to_3D(points):

    P = projection_matrix()

    pts = points @ P.T

    norm = np.linalg.norm(pts,axis=1)+1e-9

    return pts/norm[:,None]


# ----------------------------------------------------------
# 3 重力計算
# ----------------------------------------------------------

def compute_gravity(points):

    forces = np.zeros_like(points)

    for i in range(len(points)):

        diff = points - points[i]

        r = np.linalg.norm(diff,axis=1)+0.01

        f = np.sum(diff/(r[:,None]**3),axis=0)

        forces[i] = G*f

    return forces


# ----------------------------------------------------------
# 4 ダークマター近似
# ----------------------------------------------------------

def dark_matter_halo(points):

    center = np.mean(points,axis=0)

    diff = points-center

    r = np.linalg.norm(diff,axis=1)

    halo = 1/(r+0.1)

    return halo


# ----------------------------------------------------------
# 5 N体進化
# ----------------------------------------------------------

def evolve_universe(points):

    velocity = np.zeros_like(points)

    history = []

    for t in range(TIME_STEPS):

        force = compute_gravity(points)

        velocity += force*DT

        points += velocity*DT

        history.append(points.copy())

    return np.array(history)


# ----------------------------------------------------------
# 6 Cosmic Web
# ----------------------------------------------------------

def cosmic_web(points):

    nbrs = NearestNeighbors(n_neighbors=4).fit(points)

    _,indices = nbrs.kneighbors(points)

    edges = []

    for i in range(len(points)):

        for j in indices[i]:

            edges.append((i,j))

    return edges


# ----------------------------------------------------------
# 7 CMB生成
# ----------------------------------------------------------

def generate_cmb(size=256):

    noise = np.random.normal(0,1,(size,size))

    kx = fftfreq(size)

    ky = fftfreq(size)

    KX,KY = np.meshgrid(kx,ky)

    spectrum = 1/(KX**2+KY**2+0.001)

    cmb = np.real(ifft2(fft2(noise)*spectrum))

    return cmb


# ----------------------------------------------------------
# 8 重力波
# ----------------------------------------------------------

def gravitational_wave():

    t = np.linspace(0,1,4000)

    f0 = 30

    chirp = np.sin(2*np.pi*f0*t*(1+3*t))

    envelope = np.exp(3*t)

    return t, chirp*envelope


# ----------------------------------------------------------
# 宇宙生成
# ----------------------------------------------------------

print("Generating 11D Universe")

points11 = generate_high_dimension_universe()

print("Projecting to 3D")

points3 = project_to_3D(points11)

print("Evolving gravity")

history = evolve_universe(points3)

final_points = history[-1]

print("Dark matter halo")

halo = dark_matter_halo(final_points)

print("Cosmic web")

edges = cosmic_web(final_points)

print("Generating CMB")

cmb = generate_cmb()

print("Generating gravitational wave")

t,gw = gravitational_wave()


# ----------------------------------------------------------
# 可視化
# ----------------------------------------------------------

fig = plt.figure(figsize=(18,6))


# Cosmic Web

ax = fig.add_subplot(131,projection='3d')

ax.scatter(

final_points[:,0],
final_points[:,1],
final_points[:,2],

c=halo,
s=2,
alpha=0.7

)

for i,j in edges:

    ax.plot(

        [final_points[i,0],final_points[j,0]],
        [final_points[i,1],final_points[j,1]],
        [final_points[i,2],final_points[j,2]],

        linewidth=0.2,
        alpha=0.2

    )

ax.set_title("Cosmic Web + Dark Matter")


# CMB

ax2 = fig.add_subplot(132)

ax2.imshow(cmb)

ax2.axis("off")

ax2.set_title("CMB Fluctuations")


# Gravitational Wave

ax3 = fig.add_subplot(133)

ax3.plot(t,gw)

ax3.set_title("Gravitational Wave Chirp")

ax3.set_xlabel("time")

ax3.set_ylabel("strain")


plt.tight_layout()

plt.show()


print("Universe simulation finished")
