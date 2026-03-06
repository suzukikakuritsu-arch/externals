# 💊 4. 人工心臓ポンプの流量制御
class HeartPumpGERT:
    def __init__(self):
        self.G_flow, self.E_flow, self.R_flow = 0.0, 0.0, 0.1  # 流量(GER)

    def update(self, flow_error):
        # flow_error = 目標血流 - 実血流[L/min]
        g = 0.95 * (self.G_flow + self.R_flow * self.E_flow + flow_error)
        e = 0.5 * (self.E_flow + math.tanh(g))
        r = 0.1 * max(min(g / max(e, 1e-8), 1), -1)

        self.G_flow, self.E_flow, self.R_flow = g, e, r
        pump_rpm_cmd = self.G_flow * 0.236  # ポンプ回転数指令
        return pump_rpm_cmd
