# 🚗 2. 自動運転車の車線追従制御
class LaneKeepingGERT:
    def __init__(self):
        self.G_lat, self.E_lat, self.R_lat = 0.0, 0.0, 0.1  # 横方向(GER)

    def update(self, lateral_error):
        # lateral_error = 車線中心からの横ずれ[m]
        g = 0.95 * (self.G_lat + self.R_lat * self.E_lat + lateral_error)
        e = 0.5 * (self.E_lat + math.tanh(g))
        r = 0.1 * max(min(g / max(e, 1e-8), 1), -1)

        self.G_lat, self.E_lat, self.R_lat = g, e, r
        steering_cmd = self.G_lat * 0.236  # ステアリング角指令
        return steering_cmd
