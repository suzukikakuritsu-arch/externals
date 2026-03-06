# 🛰️ 6. 小型衛星の姿勢制御（1軸）
class SatelliteAttitudeGERT:
    def __init__(self):
        self.G_att, self.E_att, self.R_att = 0.0, 0.0, 0.1  # 姿勢角(GER)

    def update(self, attitude_error):
        # attitude_error = 目標姿勢 - 現姿勢[rad]
        g = 0.95 * (self.G_att + self.R_att * self.E_att + attitude_error)
        e = 0.5 * (self.E_att + math.tanh(g))
        r = 0.1 * max(min(g / max(e, 1e-8), 1), -1)

        self.G_att, self.E_att, self.R_att = g, e, r
        reaction_wheel_torque = self.G_att * 0.236
        return reaction_wheel_torque
