# 🏭 3. 産業ロボットの位置決め制御
class ArmJointGERT:
    def __init__(self):
        self.G_pos, self.E_pos, self.R_pos = 0.0, 0.0, 0.1  # 関節角(GER)

    def update(self, position_error):
        # position_error = 目標角度 - 現在角度[rad]
        g = 0.95 * (self.G_pos + self.R_pos * self.E_pos + position_error)
        e = 0.5 * (self.E_pos + math.tanh(g))
        r = 0.1 * max(min(g / max(e, 1e-8), 1), -1)

        self.G_pos, self.E_pos, self.R_pos = g, e, r
        joint_torque = self.G_pos * 0.236
        return joint_torque
