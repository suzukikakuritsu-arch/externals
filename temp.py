# 🌡️ 5. スマートエアコンの室温制御
class RoomTempGERT:
    def __init__(self):
        self.G_temp, self.E_temp, self.R_temp = 0.0, 0.0, 0.1  # 温度(GER)

    def update(self, temp_error):
        # temp_error = 目標温度 - 室温[℃]
        g = 0.95 * (self.G_temp + self.R_temp * self.E_temp + temp_error)
        e = 0.5 * (self.E_temp + math.tanh(g))
        r = 0.1 * max(min(g / max(e, 1e-8), 1), -1)

        self.G_temp, self.E_temp, self.R_temp = g, e, r
        hvac_power = self.G_temp * 0.236  # エアコン出力（-冷房/+暖房）
        return hvac_power
