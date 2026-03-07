# ==========================================================
# UNIVERSAL GOLDEN GER PHARMA QUALITY SYSTEM
# Suzuki GER + SPC + AI + PAT + Prediction
# ==========================================================

import numpy as np
import pandas as pd
from sklearn.ensemble import IsolationForest
from sklearn.linear_model import LinearRegression

# ==========================================================
# GOLDEN CONSTANT
# ==========================================================

PHI = (1 + np.sqrt(5)) / 2
DELTA_STAR = 0.236


# ==========================================================
# SUZUKI GOLDEN QC CORE
# ==========================================================

class PharmaGoldenQC:

    def __init__(self, target_mean, target_sd):

        self.target_mean = target_mean
        self.target_sd = target_sd

        self.a = 0.95
        self.r = 0.1

    def analyze_batch(self, measurements):

        df = pd.DataFrame(measurements, columns=['value'])

        # Z score
        df['z_score'] = (df['value'] - self.target_mean) / self.target_sd

        # GER components
        df['G'] = np.abs(df['z_score'])
        df['E'] = np.log(1 + df['G'])

        df['GER_ratio'] = df['G'] / df['E']

        # harmony
        df['harmony_score'] = np.exp(-np.abs(df['GER_ratio'] - PHI))

        # anomaly rule
        df['is_anomaly_phi'] = (df['z_score'].abs() > 3) | (df['harmony_score'] < DELTA_STAR)

        return df


# ==========================================================
# AI ANOMALY DETECTOR
# ==========================================================

class AIAnomaly:

    def __init__(self):

        self.model = IsolationForest(contamination=0.05)

    def detect(self,data):

        data = data.reshape(-1,1)

        self.model.fit(data)

        pred = self.model.predict(data)

        return np.where(pred == -1)[0]


# ==========================================================
# SPC
# ==========================================================

class SPC:

    def limits(self,data):

        mean = np.mean(data)
        std = np.std(data)

        UCL = mean + 3*std
        LCL = mean - 3*std

        return mean,UCL,LCL


# ==========================================================
# PREDICTION
# ==========================================================

class Predictor:

    def train(self,data):

        X = np.arange(len(data)).reshape(-1,1)
        y = data

        self.model = LinearRegression()
        self.model.fit(X,y)

    def predict(self,n=10):

        X = np.arange(n).reshape(-1,1)

        return self.model.predict(X)


# ==========================================================
# FULL SYSTEM
# ==========================================================

class GoldenPharmaSystem:

    def __init__(self,mean,sd):

        self.qc = PharmaGoldenQC(mean,sd)
        self.ai = AIAnomaly()
        self.spc = SPC()
        self.pred = Predictor()

    def run(self,data):

        values = np.array(data)

        # SPC
        mean,UCL,LCL = self.spc.limits(values)

        # GER / PHI QC
        df = self.qc.analyze_batch(values)

        # AI anomaly
        ai_anom = self.ai.detect(values)

        # prediction
        self.pred.train(values)
        future = self.pred.predict()

        print("\n--- GOLDEN GER QC REPORT ---\n")

        print(df[['value','GER_ratio','harmony_score','is_anomaly_phi']])

        print("\nSPC Limits")

        print("Mean:",mean)
        print("UCL:",UCL)
        print("LCL:",LCL)

        print("\nAI anomalies index:",ai_anom)

        print("\nPrediction:",future[:5])

        return df


# ==========================================================
# DEMO
# ==========================================================

if __name__ == "__main__":

    batch_data = [100.1, 99.8, 104.5, 100.2, 99.5, 101.1]

    system = GoldenPharmaSystem(100.0,2.0)

    report = system.run(batch_data)
