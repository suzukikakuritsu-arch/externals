# 🤖 1. 二足歩行ロボットの姿勢制御
class BipedGERTController:
    def __init__(self):
        self.G_com, self.E_com, self.R_com = 0.0, 0.0, 0.1  # 重心(GER)

    def update(self, com_error):
        # 重心誤差 com_error = 目標重心 - 実重心
        g = 0.95 * (self.G_com + self.R_com * self.E_com + com_error)
        e = 0.5 * (self.E_com + math.tanh(g))
        r = 0.1 * max(min(g / max(e, 1e-8), 1), -1)

        self.G_com, self.E_com, self.R_com = g, e, r
        ankle_torque = self.G_com * 0.236  # 足首トルク指令
        return ankle_torque
