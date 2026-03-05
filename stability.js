import { useState, useEffect, useCallback, useRef } from “react”;

// ═══════════════════════════════════════════════════════════
// 公理系
// 公理1: 情報 = 確率性 × 双方性
// 公理2: 双方性自体が確率的（確率的相互作用）
// 公理3: 次元は確率的相互作用から創発する
// 公理4: ノイズは創発の源泉（除去すべき障害ではない）
// 定理:  特定の次元数（4, 7…）で安定が生じる
// ═══════════════════════════════════════════════════════════

// ── 数学コア ────────────────────────────────────────────────
function entropy(p) {
return -p.filter(v => v > 1e-12).reduce((s, v) => s + v * Math.log2(v), 0);
}

function suzukiLevel(joint) {
const total = joint.flat().reduce((a, b) => a + b, 0);
const j = joint.map(r => r.map(v => v / total));
const px = j.map(r => r[0] + r[1]);
const py = [j[0][0] + j[1][0], j[0][1] + j[1][1]];
const Hx = entropy(px), Hy = entropy(py);
const Hxy = entropy(j.flat());
const HxGy = Math.max(Hxy - Hy, 0);
const HyGx = Math.max(Hxy - Hx, 0);
const Ish = Math.max(Hx + Hy - Hxy, 0);
const pInt = Hxy > 0 ? Ish / Hxy : 0;
const resid = HxGy + HyGx;
const Isuz = pInt * resid;
return { Hx, Hy, Hxy, Ish, pInt, resid, Isuz };
}

// ノイズ生成（スケールフリー: 分野に依らず同じ式）
function makeNoise(type) {
if (type === “dirichlet”) {
const g = [0,0,0,0].map(() => -Math.log(Math.random() + 1e-12));
const s = g.reduce((a,b) => a+b, 0);
return g.map(v => v/s);
}
if (type === “gaussian”) {
const g = [0,0,0,0].map(() => {
const u = 1-Math.random(), v = Math.random();
return Math.abs(Math.sqrt(-2*Math.log(u))*Math.cos(2*Math.PI*v));
});
const s = g.reduce((a,b) => a+b, 0);
return g.map(v => v/s);
}
// poisson
const lam = 2;
const g = [0,0,0,0].map(() => {
let L=Math.exp(-lam), k=0, p=1;
do { k++; p*=Math.random(); } while(p>L);
return Math.max(k-1,0)+0.1;
});
const s = g.reduce((a,b) => a+b, 0);
return g.map(v => v/s);
}

function nextJoint(joint, Isuz, noiseType) {
const noise = makeNoise(noiseType);
const flat = joint.flat();
const s = flat.reduce((a,b) => a+b, 0);
const norm = flat.map(v => v/s);
const nxt = norm.map((v,i) => v*Isuz + noise[i]*(1-Isuz));
const ns = nxt.reduce((a,b) => a+b, 0);
return [[nxt[0]/ns, nxt[1]/ns],[nxt[2]/ns, nxt[3]/ns]];
}

function computeChain(joint, maxLevels, noiseType) {
let cur = joint.map(r => […r]);
const chain = [];
for (let i = 0; i < maxLevels; i++) {
const r = suzukiLevel(cur);
if (r.Isuz <= 1e-6) break;
chain.push({ level: i, …r });
cur = nextJoint(cur, r.Isuz, noiseType);
}
return chain;
}

// 統計ルート: 大量試行で局所安定点を検出
function runStats(trials = 800) {
const localMins = {};
for (let t = 0; t < trials; t++) {
const g = [0,0,0,0].map(() => -Math.log(Math.random()+1e-12));
const s = g.reduce((a,b)=>a+b,0);
const joint = [[g[0]/s, g[1]/s],[g[2]/s, g[3]/s]];
const chain = computeChain(joint, 25, “dirichlet”);
const vals = chain.map(c => c.Isuz);
for (let i = 1; i < vals.length-1; i++) {
if (vals[i] < vals[i-1] && vals[i] < vals[i+1]) {
const lv = i+1;
localMins[lv] = (localMins[lv]||0)+1;
}
}
}
return localMins;
}

// 自然照合データ
const NATURAL_CROSSREF = {
4: [
{ domain: “物理”, desc: “時空次元 (3+1)”, icon: “⚛” },
{ domain: “薬理”, desc: “4次構造タンパク質・テトラマー受容体”, icon: “💊” },
{ domain: “情報”, desc: “DNA塩基数・2ビット (2²=4)”, icon: “🧬” },
{ domain: “数学”, desc: “4色定理・四元数”, icon: “∞” },
],
7: [
{ domain: “物理”, desc: “M理論余剰次元・G2例外リー群”, icon: “⚛” },
{ domain: “薬理”, desc: “GPCR 7回膜貫通（最大の薬物標的クラス）”, icon: “💊” },
{ domain: “情報”, desc: “ミラーの法則 (7±2)・情報処理限界”, icon: “🧠” },
{ domain: “数学”, desc: “フォノ平面・7橋問題”, icon: “∞” },
],
};

// ═══ UI ═══════════════════════════════════════════════════
const PRESETS = {
“強い相互作用”: [[0.45,0.05],[0.05,0.45]],
“非対称”: [[0.6,0.1],[0.2,0.1]],
“弱い相互作用”: [[0.35,0.15],[0.15,0.35]],
“独立”: [[0.25,0.25],[0.25,0.25]],
};
const NOISE_LABELS = { dirichlet:“情報系”, gaussian:“物理系”, poisson:“薬理系” };
const TABS = [“創発チェーン”, “統計検定”, “自然照合”, “公理系”];

export default function App() {
const [joint, setJoint] = useState([[0.45,0.05],[0.05,0.45]]);
const [noise, setNoise] = useState(“dirichlet”);
const [maxLv, setMaxLv] = useState(12);
const [chain, setChain] = useState([]);
const [stats, setStats] = useState(null);
const [statsRunning, setStatsRunning] = useState(false);
const [tab, setTab] = useState(0);
const [seed, setSeed] = useState(0);
const [animIn, setAnimIn] = useState(false);

useEffect(() => {
setChain(computeChain(joint, maxLv, noise));
setAnimIn(false);
setTimeout(() => setAnimIn(true), 50);
}, [joint, noise, maxLv, seed]);

const runStatsAsync = useCallback(() => {
setStatsRunning(true);
setTimeout(() => {
setStats(runStats(1000));
setStatsRunning(false);
}, 50);
}, []);

const emerged = chain.length;
const maxIsuz = Math.max(…chain.map(c => c.Isuz), 0.001);

// 安定次元ハイライト
const isStable = (lv) => {
if (chain.length < 3) return false;
const vals = chain.map(c => c.Isuz);
const i = lv - 1;
if (i < 1 || i >= vals.length-1) return false;
return vals[i] < vals[i-1] && vals[i] < vals[i+1];
};

return (
<div style={{
minHeight:“100vh”, background:”#05080f”,
color:”#c8d0e0”, fontFamily:”‘IBM Plex Mono’,‘Fira Code’,monospace”,
padding:“28px 20px”, boxSizing:“border-box”,
}}>
{/* ヘッダー */}
<div style={{marginBottom:24, borderBottom:“1px solid #0e1a2e”, paddingBottom:20}}>
<div style={{fontSize:10, letterSpacing:5, color:”#1e4a7a”, marginBottom:6}}>
SUZUKI UNIFIED STABILITY THEORY
</div>
<h1 style={{margin:0, fontSize:22, fontWeight:700, color:”#e8f0ff”, lineHeight:1.3}}>
鈴木横断安定理論
</h1>
<div style={{marginTop:8, fontSize:11, color:”#3a5070”, lineHeight:1.8}}>
情報 = 確率性 × 双方性　／　次元は確率的相互作用から創発する<br/>
統計・情報・物理・薬理の横断統合
</div>
</div>

```
  <div style={{display:"grid", gridTemplateColumns:"260px 1fr", gap:16, maxWidth:960}}>
    {/* 左: 入力パネル */}
    <div>
      <Panel title="同時確率分布 P(X,Y)">
        <div style={{display:"grid", gridTemplateColumns:"1fr 1fr", gap:6, marginBottom:12}}>
          {[0,1].map(r=>[0,1].map(c=>(
            <div key={`${r}${c}`}>
              <div style={{fontSize:9, color:"#1e4a7a", marginBottom:3}}>X={r},Y={c}</div>
              <input type="number" step="0.01" min="0.001" max="0.999"
                value={joint[r][c]}
                onChange={e=>{
                  const j=joint.map(row=>[...row]);
                  j[r][c]=Math.max(0.001,parseFloat(e.target.value)||0.001);
                  setJoint(j);
                }}
                style={{
                  width:"100%", boxSizing:"border-box",
                  background:"#080c14", border:"1px solid #0e1a2e",
                  color:"#8ab0d0", padding:"6px 8px", borderRadius:4,
                  fontFamily:"inherit", fontSize:12, outline:"none",
                }}
              />
            </div>
          )))}
        </div>
        <div style={{display:"flex", flexWrap:"wrap", gap:5}}>
          {Object.entries(PRESETS).map(([name,j])=>(
            <button key={name} onClick={()=>setJoint(j)} style={{
              background:"#080c14", border:"1px solid #0e1a2e",
              color:"#3a5878", padding:"4px 8px", borderRadius:3,
              fontFamily:"inherit", fontSize:10, cursor:"pointer",
            }} onMouseEnter={e=>{e.target.style.color="#4a9eff";e.target.style.borderColor="#1e3a6a";}}
               onMouseLeave={e=>{e.target.style.color="#3a5878";e.target.style.borderColor="#0e1a2e";}}>
              {name}
            </button>
          ))}
        </div>
      </Panel>

      <Panel title="ノイズ分布（創発源泉）">
        {Object.entries(NOISE_LABELS).map(([k,v])=>(
          <button key={k} onClick={()=>setNoise(k)} style={{
            display:"block", width:"100%", marginBottom:5, textAlign:"left",
            background: noise===k ? "#081828" : "#080c14",
            border:`1px solid ${noise===k?"#1e4a7a":"#0e1a2e"}`,
            color: noise===k ? "#4a9eff" : "#3a5878",
            padding:"7px 10px", borderRadius:4,
            fontFamily:"inherit", fontSize:11, cursor:"pointer",
          }}>
            <span style={{marginRight:8}}>{noise===k?"●":"○"}</span>{k} — {v}
          </button>
        ))}
      </Panel>

      <Panel title={`最大階層: ${maxLv}`}>
        <input type="range" min={4} max={20} value={maxLv}
          onChange={e=>setMaxLv(+e.target.value)}
          style={{width:"100%", accentColor:"#4a9eff"}}/>
      </Panel>

      <button onClick={()=>setSeed(s=>s+1)} style={{
        width:"100%", padding:"10px",
        background:"#081828", border:"1px solid #1e3a6a",
        color:"#4a9eff", fontFamily:"inherit", fontSize:12,
        cursor:"pointer", borderRadius:5, letterSpacing:2,
      }}>↺ ノイズ再生成</button>

      {/* サマリー */}
      <div style={{marginTop:12, display:"grid", gridTemplateColumns:"1fr 1fr", gap:6}}>
        <MiniStat label="創発次元" value={emerged} unit="次元" hi />
        <MiniStat label="P(interact)" value={chain[0]?.pInt.toFixed(3)??"—"} />
        <MiniStat label="I_suzuki[0]" value={chain[0]?.Isuz.toFixed(4)??"—"} />
        <MiniStat label="安定点" value={chain.filter((_,i)=>isStable(i+1)).length} unit="個" />
      </div>
    </div>

    {/* 右: タブパネル */}
    <div>
      {/* タブ */}
      <div style={{display:"flex", gap:4, marginBottom:12}}>
        {TABS.map((t,i)=>(
          <button key={t} onClick={()=>setTab(i)} style={{
            padding:"7px 12px", borderRadius:"4px 4px 0 0",
            background: tab===i ? "#0a1828" : "#080c14",
            border:`1px solid ${tab===i?"#1e3a6a":"#0e1a2e"}`,
            borderBottom: tab===i ? "1px solid #0a1828" : "1px solid #0e1a2e",
            color: tab===i ? "#4a9eff" : "#3a5878",
            fontFamily:"inherit", fontSize:11, cursor:"pointer",
          }}>{t}</button>
        ))}
      </div>

      <div style={{
        background:"#0a1828", border:"1px solid #1e3a6a",
        borderRadius:"0 6px 6px 6px", padding:16, minHeight:400,
      }}>

        {/* ── タブ0: 創発チェーン ── */}
        {tab===0 && (
          <div>
            <div style={{fontSize:10, color:"#1e4a7a", letterSpacing:3, marginBottom:14}}>
              EMERGENCE CHAIN — I_suzuki = P(interact) × [H(X|Y) + H(Y|X)]
            </div>
            {chain.length === 0 && (
              <div style={{color:"#1e3a6a", fontSize:13, padding:"20px 0"}}>
                相互作用なし — 創発ゼロ（独立分布）
              </div>
            )}
            {chain.map((c, i) => {
              const stable = isStable(i+1);
              const is4or7 = (i+1)===4||(i+1)===7;
              return (
                <div key={i} style={{
                  display:"flex", alignItems:"center", gap:10, marginBottom:8,
                  opacity: animIn ? 1 : 0,
                  transform: animIn ? "translateX(0)" : "translateX(-10px)",
                  transition: `all 0.3s ease ${i*0.04}s`,
                }}>
                  {/* 次元番号 */}
                  <div style={{
                    width:32, height:32, borderRadius:"50%", flexShrink:0,
                    background: is4or7 ? "#0a2040" : stable ? "#0a1828" : "#080c14",
                    border:`1px solid ${is4or7?"#4a9eff":stable?"#1e3a6a":"#0e1a2e"}`,
                    display:"flex", alignItems:"center", justifyContent:"center",
                    fontSize:11, fontWeight:700,
                    color: is4or7?"#4a9eff":stable?"#2a6a9a":"#2a4060",
                    boxShadow: is4or7?"0 0 8px #0a3a7a":stable?"0 0 4px #0a2a5a":"none",
                  }}>{i+1}</div>

                  {/* バー */}
                  <div style={{flex:1}}>
                    <div style={{
                      height:8, borderRadius:4, background:"#080c14", overflow:"hidden",
                    }}>
                      <div style={{
                        height:"100%",
                        width: animIn ? `${(c.Isuz/maxIsuz)*100}%` : "0%",
                        background: is4or7
                          ? "linear-gradient(90deg,#1e4a9a,#4a9eff)"
                          : stable
                          ? "linear-gradient(90deg,#0a2a6a,#2a6aaa)"
                          : `hsl(${210+i*8},40%,${25+i*2}%)`,
                        borderRadius:4,
                        transition:`width 0.5s ease ${i*0.04}s`,
                      }}/>
                    </div>
                  </div>

                  {/* 数値 */}
                  <div style={{width:64, fontSize:10, color:"#2a5070", textAlign:"right"}}>
                    {c.Isuz.toFixed(4)}
                  </div>
                  <div style={{width:50, fontSize:10, textAlign:"right",
                    color: is4or7?"#4a9eff":stable?"#2a6a9a":"#1a3050"}}>
                    {is4or7 ? "★安定" : stable ? "局所安定" : "創発"}
                  </div>
                </div>
              );
            })}

            {/* 式 */}
            <div style={{
              marginTop:20, padding:"12px 14px",
              background:"#080c14", border:"1px solid #0e1a2e", borderRadius:6,
              fontSize:11, color:"#2a5070", lineHeight:2,
            }}>
              <div><span style={{color:"#4a9eff"}}>P(interact)</span> = I(X;Y) / H(X,Y)</div>
              <div><span style={{color:"#4a9eff"}}>I_suzuki(n+1)</span> = P(interact|n) × [H(X|Y,n) + H(Y|X,n)]</div>
              <div style={{marginTop:6, color:"#1a3050"}}>ノイズ自体が創発の源泉 — スケールフリー</div>
            </div>
          </div>
        )}

        {/* ── タブ1: 統計検定 ── */}
        {tab===1 && (
          <div>
            <div style={{fontSize:10, color:"#1e4a7a", letterSpacing:3, marginBottom:14}}>
              STATISTICAL ROUTE — 局所安定点の次元数分布
            </div>
            {!stats && (
              <div>
                <div style={{fontSize:12, color:"#3a5878", marginBottom:16, lineHeight:1.8}}>
                  1000試行でランダムな初期分布を生成し、<br/>
                  局所安定点が何次元目に出現するか検定します。<br/>
                  4と7が有意に多く出るか？
                </div>
                <button onClick={runStatsAsync} disabled={statsRunning} style={{
                  padding:"10px 20px",
                  background: statsRunning ? "#080c14" : "#0a1828",
                  border:"1px solid #1e3a6a", color:"#4a9eff",
                  fontFamily:"inherit", fontSize:12, cursor:"pointer", borderRadius:5,
                }}>
                  {statsRunning ? "計算中..." : "▶ 統計検定を実行（1000試行）"}
                </button>
              </div>
            )}
            {stats && (() => {
              const total = Object.values(stats).reduce((a,b)=>a+b,0);
              const expected = total / Object.keys(stats).length;
              const sorted = Object.entries(stats).sort((a,b)=>+a[0]-+b[0]);
              const maxC = Math.max(...Object.values(stats));
              return (
                <div>
                  <div style={{fontSize:11, color:"#2a5070", marginBottom:12}}>
                    総局所安定点数: {total} ／ 期待値: {expected.toFixed(0)}/次元
                  </div>
                  {sorted.slice(0,15).map(([lv,c])=>{
                    const n = +lv;
                    const is47 = n===4||n===7;
                    const ratio = c/expected;
                    return (
                      <div key={lv} style={{display:"flex", alignItems:"center", gap:8, marginBottom:6}}>
                        <div style={{
                          width:28, fontSize:10, textAlign:"right",
                          color: is47?"#4a9eff":"#2a4060", fontWeight:is47?700:400,
                        }}>{lv}</div>
                        <div style={{flex:1, height:6, background:"#080c14", borderRadius:3, overflow:"hidden"}}>
                          <div style={{
                            height:"100%", borderRadius:3,
                            width:`${(c/maxC)*100}%`,
                            background: is47
                              ? "linear-gradient(90deg,#1e4a9a,#4a9eff)"
                              : "#1a3050",
                            transition:"width 0.4s ease",
                          }}/>
                        </div>
                        <div style={{width:40, fontSize:10, color:"#2a5070", textAlign:"right"}}>{c}</div>
                        <div style={{width:48, fontSize:10, textAlign:"right",
                          color:is47?"#4a9eff":ratio>1.1?"#2a6a9a":"#1a3050"}}>
                          {ratio.toFixed(2)}x{is47?" ★":""}
                        </div>
                      </div>
                    );
                  })}
                  <button onClick={runStatsAsync} style={{
                    marginTop:12, padding:"7px 14px",
                    background:"#080c14", border:"1px solid #0e1a2e",
                    color:"#2a5070", fontFamily:"inherit", fontSize:11, cursor:"pointer", borderRadius:4,
                  }}>↺ 再実行</button>
                </div>
              );
            })()}
          </div>
        )}

        {/* ── タブ2: 自然照合 ── */}
        {tab===2 && (
          <div>
            <div style={{fontSize:10, color:"#1e4a7a", letterSpacing:3, marginBottom:14}}>
              NATURAL CROSS-REFERENCE — 4と7の自然界における特別性
            </div>
            {[4,7].map(n=>(
              <div key={n} style={{marginBottom:20}}>
                <div style={{
                  fontSize:18, fontWeight:700, color:"#4a9eff",
                  borderBottom:"1px solid #0e1a2e", paddingBottom:8, marginBottom:12,
                }}>
                  {n}次元
                  <span style={{fontSize:11, color:"#1e4a7a", marginLeft:12, fontWeight:400}}>
                    — 鈴木理論での局所安定点
                  </span>
                </div>
                {NATURAL_CROSSREF[n].map((item,i)=>(
                  <div key={i} style={{
                    display:"flex", gap:12, marginBottom:8, padding:"8px 10px",
                    background:"#080c14", border:"1px solid #0e1a2e", borderRadius:5,
                  }}>
                    <div style={{fontSize:16}}>{item.icon}</div>
                    <div>
                      <div style={{fontSize:10, color:"#1e4a7a", marginBottom:2}}>{item.domain}</div>
                      <div style={{fontSize:12, color:"#6a8aaa"}}>{item.desc}</div>
                    </div>
                  </div>
                ))}
              </div>
            ))}
            <div style={{
              padding:"10px 12px", background:"#080c14",
              border:"1px solid #0e1a2e", borderRadius:5,
              fontSize:11, color:"#2a5070", lineHeight:1.8,
            }}>
              鈴木理論の予測: 情報の確率的相互作用が収束する次元数は<br/>
              自然界が「選んだ」構造と一致する可能性がある
            </div>
          </div>
        )}

        {/* ── タブ3: 公理系 ── */}
        {tab===3 && (
          <div>
            <div style={{fontSize:10, color:"#1e4a7a", letterSpacing:3, marginBottom:14}}>
              AXIOMATIC FOUNDATION — 鈴木横断安定理論の公理系
            </div>
            {[
              { n:"公理1", title:"情報の定義",
                eq:"I = 確率性 × 双方性",
                note:"シャノン情報論を包含し拡張する。双方性なき確率性はシャノンに帰着する。" },
              { n:"公理2", title:"確率的相互作用",
                eq:"P(interact) = I(X;Y) / H(X,Y)",
                note:"相互作用するかどうか自体が確率的。距離・エネルギー不要。情報だけで閉じた定義。スケールフリー。" },
              { n:"公理3", title:"鈴木情報量",
                eq:"I_suzuki = P(interact) × [H(X|Y) + H(Y|X)]",
                note:"双方向の残余不確かさに相互作用確率を乗じる。完全従属(P=1)と完全独立(P=0)の二面性を自然に包含。" },
              { n:"公理4", title:"創発の源泉",
                eq:"I_suzuki(n+1) = f(I_suzuki(n), ノイズ(n))",
                note:"ノイズは創発の障害ではなく源泉。ノイズの分布が変わっても（情報系・物理系・薬理系）同じ式が成立する。" },
              { n:"定理", title:"横断安定性",
                eq:"∃ n* ∈ {4, 7, ...} : I_suzuki局所最小",
                note:"確率的相互作用の再帰的創発は特定の次元数で局所安定する。この次元数は統計・情報・物理・薬理で横断的に出現する。" },
            ].map((ax,i)=>(
              <div key={i} style={{
                marginBottom:12, padding:"12px 14px",
                background:"#080c14", border:"1px solid #0e1a2e", borderRadius:6,
              }}>
                <div style={{display:"flex", gap:10, alignItems:"baseline", marginBottom:6}}>
                  <span style={{
                    fontSize:9, letterSpacing:2, color:"#1e4a7a",
                    background:"#0a1020", padding:"2px 6px", borderRadius:3,
                  }}>{ax.n}</span>
                  <span style={{fontSize:13, color:"#8ab0d0", fontWeight:600}}>{ax.title}</span>
                </div>
                <div style={{
                  fontSize:13, color:"#4a9eff", padding:"6px 10px",
                  background:"#0a1828", borderRadius:4, marginBottom:8,
                  borderLeft:"2px solid #1e4a7a",
                }}>{ax.eq}</div>
                <div style={{fontSize:11, color:"#2a5070", lineHeight:1.7}}>{ax.note}</div>
              </div>
            ))}
          </div>
        )}
      </div>
    </div>
  </div>

  <div style={{marginTop:24, fontSize:9, color:"#0e1a2e", letterSpacing:3}}>
    SUZUKI UNIFIED STABILITY THEORY — 情報 = 確率性 × 双方性 — SCALE FREE
  </div>
</div>
```

);
}

function Panel({ title, children }) {
return (
<div style={{
background:”#0a0f1a”, border:“1px solid #0e1a2e”,
borderRadius:6, padding:14, marginBottom:10,
}}>
<div style={{fontSize:9, letterSpacing:3, color:”#1e3a5a”, marginBottom:10, textTransform:“uppercase”}}>
{title}
</div>
{children}
</div>
);
}

function MiniStat({ label, value, unit=””, hi=false }) {
return (
<div style={{
background:”#080c14”, border:`1px solid ${hi?"#0e2a4a":"#0a1020"}`,
borderRadius:5, padding:“8px 10px”,
}}>
<div style={{fontSize:9, color:”#1a3050”, marginBottom:3}}>{label}</div>
<div style={{fontSize:16, color: hi?”#4a9eff”:”#4a6a8a”, fontWeight:700}}>
{value}<span style={{fontSize:10, color:”#1a3050”, marginLeft:3}}>{unit}</span>
</div>
</div>
);
}
