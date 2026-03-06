# 🎮 7. ゲームAIのターゲット追従（カメラ/照準）
class AimAssistGERT:
    def __init__(self):
        self.G_aim, self.E_aim, self.R_aim = 0.0, 0.0, 0.1  # 画面上誤差(GER)

    def update(self, cursor_error):
        # cursor_error = ターゲット - 照準位置[ピクセル]
        g = 0.95 * (self.G_aim + self.R_aim * self.E_aim + cursor_error)
        e = 0.5 * (self.E_aim + math.tanh(g))
        r = 0.1 * max(min(g / max(e, 1e-8), 1), -1)

        self.G_aim, self.E_aim, self.R_aim = g, e, r
        cursor_velocity_cmd = self.G_aim * 0.236
        return cursor_velocity_cmd

# 📡 8. アンテナ指向制御（衛星通信）
class AntennaGERT:
    def __init__(self):
        self.G_az, self.E_az, self.R_az = 0.0, 0.0, 0.1  # 方位角(GER)

    def update(self, azimuth_error):
        # azimuth_error = 目標方位 - 現在方位[deg]
        g = 0.95 * (self.G_az + self.R_az * self.E_az + azimuth_error)
        e = 0.5 * (self.E_az + math.tanh(g))
        r = 0.1 * max(min(g / max(e, 1e-8), 1), -1)

        self.G_az, self.E_az, self.R_az = g, e, r
        motor_cmd = self.G_az * 0.236
        return motor_cmd

# 🌱 9. 精密農業ドローンの高度＋散布量制御（2chの例）
class AgroDroneGERT:
    def __init__(self):
        self.alt = GERT()   # 高度用
        self.spray = GERT() # 散布量用

    def update(self, alt_error, dose_error):
        thrust_cmd = self.alt.control(alt_error)        # 推力指令
        pump_cmd   = self.spray.control(dose_error)     # ポンプ指令
        return thrust_cmd, pump_cmd

# 🎼 10. オーディオDSPの自動音量安定化
class AudioLevelGERT:
    def __init__(self):
        self.G_lvl, self.E_lvl, self.R_lvl = 0.0, 0.0, 0.1  # 音量レベル(GER)

    def update(self, level_error):
        # level_error = 目標ラウドネス - 実ラウドネス[dB]
        g = 0.95 * (self.G_lvl + self.R_lvl * self.E_lvl + level_error)
        e = 0.5 * (self.E_lvl + math.tanh(g))
        r = 0.1 * max(min(g / max(e, 1e-8), 1), -1)

        self.G_lvl, self.E_lvl, self.R_lvl = g, e, r
        gain_cmd = self.G_lvl * 0.236  # 自動ゲイン調整量
        return gain_cmd

