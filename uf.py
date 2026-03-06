class UniverseFusion:
    def __init__(self):
        self.universeA = GERT()  # 宇宙A
        self.universeB = GERT()  # 宇宙B
        
    def fuse(self):
        # ブラックホール融合
        g_fused = 0.95 * (self.universeA.G + self.universeB.G)
        e_fused = 0.5 * math.tanh(g_fused)
        r_fused = 0.1 * max(min(g_fused/e_fused, 1), -1)
        
        # 新宇宙誕生
        new_universe = GERT()
        new_universe.G, new_universe.E, new_universe.R = g_fused, e_fused, r_fused
        return new_universe
