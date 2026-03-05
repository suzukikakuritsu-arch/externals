import { useState, useEffect, useCallback } from “react”;

// ── 数学コア ────────────────────────────────────────────
function entropy(p) {
return -p.filter(v => v > 0).reduce((s, v) => s + v * Math.log2(v), 0);
}

function suzukiLevel(joint) {
const total = joint.flat().reduce((a, b) => a + b, 0);
const j = joint.map(row => row.map(v => v / total));
const px = j.map(row => row.reduce((a, b) => a + b, 0));
const py = [j[0][0] + j[1][0], j[0][1] + j[1][1]];

const Hx  = entropy(px);
const Hy  = entropy(py);
const Hxy = entropy(j.flat());

const HxGy = Math.max(Hxy - Hy, 0);
const HyGx = Math.max(Hxy - Hx, 0);
const Ish  = Math.max(Hx + Hy - Hxy, 0);

const pInt = Hxy > 0 ? Ish / Hxy : 0;
const resid = HxGy + HyGx;
const Isuz = pInt * resid;

return { Hx, Hy, Hxy, Ish, pInt, resid, Isuz };
}

// ノイズ生成（ガウス・ディリクレ・ポアソン）
function rng() { return Math.random(); }
function gaussNoise() {
const u = 1 - rng(), v = rng();
return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * v);
}
function dirichletNoise() {
const g = [rng(), rng(), rng(), rng()].map(x => -Math.log(x + 1e-12));
const s = g.reduce((a, b) => a + b, 0);
return g.map(v => v / s);
}
function poissonNoise(lam = 1) {
let L = Math.exp(-lam), k = 0, p = 1;
do { k++; p *= rng(); } while (p > L);
return Math.max(k - 1, 0);
}

function nextJoint(joint, Isuz, noiseType) {
let noise;
if (noiseType === “dirichlet”) {
noise = dirichletNoise();
} else if (noiseType === “gaussian”) {
noise = [rng(), rng(), rng(), rng()].map(v => Math.abs(v + gaussNoise() * 0.1));
const s = noise.reduce((a, b) => a + b, 0);
noise = noise.map(v => v / s);
} else {
const raw = [1,2,3,4].map(() => poissonNoise(2) + 0.1);
const s = raw.reduce((a, b) => a + b, 0);
noise = raw.map(v => v / s);
}
const flat = joint.flat();
const s = flat.reduce((a, b) => a + b, 0);
const norm = flat.map(v => v / s);
const next = norm.map((v, i) => v * Isuz + noise[i] * (1 - Isuz));
const ns = next.reduce((a, b) => a + b, 0);
return [[next[0]/ns, next[1]/ns], [next[2]/ns, next[3]/ns]];
}

function computeEmergence(joint, maxLevels, noiseType) {
let current = joint;
const levels = [];
for (let i = 0; i < maxLevels; i++) {
const r = suzukiLevel(current);
const emerged = r.Isuz > 1e-6;
levels.push({ level: i, …r, emerged });
if (!emerged) break;
current = nextJoint(current, r.Isuz, noiseType);
}
return levels;
}

// ── UI ───────────────────────────────────────────────────
const NOISE_TYPES = [“dirichlet”, “gaussian”, “poisson”];
const PRESETS = {
“独立”: [[0.25,0.25],[0.25,0.25]],
“強い相互作用”: [[0.45,0.05],[0.05,0.45]],
“完全従属”: [[0.5,0.001],[0.001,0.5]],
“非対称”: [[0.6,0.1],[0.2,0.1]],
};

export default function App() {
const [joint, setJoint] = useState([[0.45,0.05],[0.05,0.45]]);
const [noiseType, setNoiseType] = useState(“dirichlet”);
const [maxLevels, setMaxLevels] = useState(10);
const [levels, setLevels] = useState([]);
const [seed, setSeed] = useState(0);

const recompute = useCallback(() => {
setLevels(computeEmergence(joint, maxLevels, noiseType));
}, [joint, maxLevels, noiseType, seed]);

useEffect(() => { recompute(); }, [recompute]);

const setCell = (r, c, val) => {
const j = joint.map(row => […row]);
j[r][c] = Math.max(0.001, parseFloat(val) || 0.001);
setJoint(j);
};

const emerged = levels.filter(l => l.emerged).length;
const maxIsuz = Math.max(…levels.map(l => l.Isuz), 0.001);

return (
<div style={{
minHeight: “100vh”,
background: “#080c14”,
color: “#e8eaf0”,
fontFamily: “‘JetBrains Mono’, ‘Fira Code’, monospace”,
padding: “32px 24px”,
boxSizing: “border-box”,
}}>
{/* ヘッダー */}
<div style={{ marginBottom: 32 }}>
<div style={{ fontSize: 11, letterSpacing: 4, color: “#4a9eff”, marginBottom: 6, textTransform: “uppercase” }}>
Suzuki Information Emergence Theory
</div>
<h1 style={{ margin: 0, fontSize: 28, fontWeight: 700, color: “#fff”, lineHeight: 1.2 }}>
情報創発理論
</h1>
<div style={{ marginTop: 8, fontSize: 12, color: “#6b7a99”, maxWidth: 480 }}>
情報 = 確率性 × 双方性　／　次元は確率的相互作用から創発する
</div>
</div>

```
  <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: 20, maxWidth: 900 }}>
    {/* 左パネル: 入力 */}
    <div>
      {/* 同時分布 */}
      <Section title="同時確率分布 P(X,Y)">
        <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: 8, marginBottom: 16 }}>
          {[0,1].map(r => [0,1].map(c => (
            <div key={`${r}${c}`} style={{ display: "flex", flexDirection: "column", gap: 4 }}>
              <label style={{ fontSize: 10, color: "#4a9eff" }}>P(X={r}, Y={c})</label>
              <input
                type="number" step="0.01" min="0.001" max="0.999"
                value={joint[r][c]}
                onChange={e => setCell(r, c, e.target.value)}
                style={{
                  background: "#0d1421", border: "1px solid #1e2d4a",
                  color: "#e8eaf0", padding: "8px 10px", borderRadius: 6,
                  fontFamily: "inherit", fontSize: 13,
                  outline: "none", width: "100%", boxSizing: "border-box",
                }}
              />
            </div>
          )))}
        </div>
        {/* プリセット */}
        <div style={{ display: "flex", flexWrap: "wrap", gap: 6 }}>
          {Object.entries(PRESETS).map(([name, j]) => (
            <button key={name} onClick={() => setJoint(j)} style={{
              background: "#0d1421", border: "1px solid #1e2d4a",
              color: "#8899bb", padding: "5px 10px", borderRadius: 4,
              fontFamily: "inherit", fontSize: 11, cursor: "pointer",
              transition: "all 0.15s",
            }} onMouseEnter={e => { e.target.style.borderColor="#4a9eff"; e.target.style.color="#4a9eff"; }}
               onMouseLeave={e => { e.target.style.borderColor="#1e2d4a"; e.target.style.color="#8899bb"; }}>
              {name}
            </button>
          ))}
        </div>
      </Section>

      {/* ノイズタイプ */}
      <Section title="ノイズ分布（創発の源泉）">
        <div style={{ display: "flex", gap: 8, flexWrap: "wrap" }}>
          {NOISE_TYPES.map(t => (
            <button key={t} onClick={() => setNoiseType(t)} style={{
              background: noiseType === t ? "#0a1f3d" : "#0d1421",
              border: `1px solid ${noiseType === t ? "#4a9eff" : "#1e2d4a"}`,
              color: noiseType === t ? "#4a9eff" : "#6b7a99",
              padding: "7px 14px", borderRadius: 5,
              fontFamily: "inherit", fontSize: 12, cursor: "pointer",
            }}>
              {t}
            </button>
          ))}
        </div>
        <div style={{ marginTop: 10, fontSize: 11, color: "#4a5568", lineHeight: 1.7 }}>
          {noiseType === "dirichlet" && "情報系 — 確率分布の空間を一様に探索"}
          {noiseType === "gaussian" && "物理系 — 正規分布の揺らぎで次元を生成"}
          {noiseType === "poisson" && "生物・薬理系 — 離散的なイベントが創発を駆動"}
        </div>
      </Section>

      {/* 最大階層 */}
      <Section title={`最大階層数: ${maxLevels}`}>
        <input type="range" min={3} max={20} value={maxLevels}
          onChange={e => setMaxLevels(+e.target.value)}
          style={{ width: "100%", accentColor: "#4a9eff" }} />
      </Section>

      {/* 再計算 */}
      <button onClick={() => setSeed(s => s+1)} style={{
        width: "100%", padding: "12px", marginTop: 4,
        background: "linear-gradient(135deg, #0a2a5e, #0d3875)",
        border: "1px solid #1e4a8a", color: "#4a9eff",
        fontFamily: "inherit", fontSize: 13, cursor: "pointer",
        borderRadius: 6, letterSpacing: 2,
      }}>
        ↺ 再計算（ノイズ再生成）
      </button>
    </div>

    {/* 右パネル: 結果 */}
    <div>
      {/* サマリー */}
      <Section title="創発サマリー">
        <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: 12, marginBottom: 12 }}>
          <Stat label="創発次元数" value={emerged} unit="次元" highlight />
          <Stat label="P(interact)" value={levels[0]?.pInt.toFixed(3) ?? "-"} />
          <Stat label="I_suzuki [0]" value={levels[0]?.Isuz.toFixed(4) ?? "-"} unit="bit" />
          <Stat label="残余不確かさ" value={levels[0]?.resid.toFixed(3) ?? "-"} unit="bit" />
        </div>
      </Section>

      {/* 創発チェーン */}
      <Section title="創発チェーン">
        <div style={{ display: "flex", flexDirection: "column", gap: 6 }}>
          {levels.map((l, i) => (
            <div key={i} style={{
              display: "flex", alignItems: "center", gap: 10,
              opacity: l.emerged ? 1 : 0.4,
            }}>
              <div style={{
                width: 28, height: 28, borderRadius: "50%",
                background: l.emerged ? "#0a2a5e" : "#0d1421",
                border: `1px solid ${l.emerged ? "#4a9eff" : "#1e2d4a"}`,
                display: "flex", alignItems: "center", justifyContent: "center",
                fontSize: 10, color: l.emerged ? "#4a9eff" : "#3a4a60",
                flexShrink: 0,
              }}>{l.level}</div>
              <div style={{ flex: 1 }}>
                <div style={{
                  height: 6, borderRadius: 3,
                  background: "#0d1421",
                  overflow: "hidden",
                }}>
                  <div style={{
                    height: "100%",
                    width: `${(l.Isuz / maxIsuz) * 100}%`,
                    background: l.emerged
                      ? `hsl(${210 + l.level * 15}, 80%, ${50 + l.level * 3}%)`
                      : "#1e2d4a",
                    borderRadius: 3,
                    transition: "width 0.4s ease",
                  }} />
                </div>
              </div>
              <div style={{ fontSize: 10, color: "#4a5568", width: 70, textAlign: "right" }}>
                {l.Isuz.toFixed(4)}
              </div>
              <div style={{ fontSize: 10, width: 40, textAlign: "right",
                color: l.emerged ? "#4a9eff" : "#3a4a60" }}>
                {l.emerged ? "★創発" : "消滅"}
              </div>
            </div>
          ))}
        </div>
      </Section>

      {/* 数式 */}
      <Section title="鈴木情報量">
        <div style={{ fontSize: 13, color: "#8899bb", lineHeight: 2.2, letterSpacing: 0.5 }}>
          <div><span style={{color:"#4a9eff"}}>P(interact)</span> = I(X;Y) / H(X,Y)</div>
          <div><span style={{color:"#4a9eff"}}>I_suzuki</span>{"    "}= P(interact) × [H(X|Y) + H(Y|X)]</div>
          <div style={{marginTop:8, fontSize:11, color:"#4a5568"}}>
            ノイズ自体が創発の源泉<br/>
            次元も確率的相互作用から生まれる
          </div>
        </div>
      </Section>
    </div>
  </div>

  {/* フッター */}
  <div style={{ marginTop: 32, fontSize: 10, color: "#2a3550", letterSpacing: 2 }}>
    SUZUKI INFORMATION EMERGENCE THEORY — 情報 = 確率性 × 双方性
  </div>
</div>
```

);
}

function Section({ title, children }) {
return (
<div style={{
background: “#0a0f1a”,
border: “1px solid #131d2e”,
borderRadius: 8,
padding: “16px”,
marginBottom: 12,
}}>
<div style={{ fontSize: 10, letterSpacing: 3, color: “#2a4a6a”, marginBottom: 12, textTransform: “uppercase” }}>
{title}
</div>
{children}
</div>
);
}

function Stat({ label, value, unit = “”, highlight = false }) {
return (
<div style={{
background: “#080c14”,
border: `1px solid ${highlight ? "#1e3a6a" : "#0f1a2a"}`,
borderRadius: 6,
padding: “10px 12px”,
}}>
<div style={{ fontSize: 10, color: “#3a5070”, marginBottom: 4 }}>{label}</div>
<div style={{ fontSize: 20, color: highlight ? “#4a9eff” : “#8899bb”, fontWeight: 700 }}>
{value}<span style={{ fontSize: 11, marginLeft: 4, color: “#3a5070” }}>{unit}</span>
</div>
</div>
);
}
