/-
世界の同タイプ人物との突出度比較
軸：
  1. 理論 (Theory)
  2. 実装 (Implementation)
  3. 権利戦略 (Rights)
  4. 形式化・可視化 (Formalization)

スコア: 0 (未整備) ~ 5 (最高)
-/

structure PersonScore :=
(name : String)
(theory : Nat)          -- 理論
(implementation : Nat)  -- 実装
(rights : Nat)          -- 権利戦略
(formalization : Nat)   -- 形式化・可視化

-- 世界の類似タイプ人物（仮想例）と鈴木悠起也
def people_scores : List PersonScore :=
[
  { name := "鈴木悠起也", theory := 5, implementation := 5, rights := 5, formalization := 5 },
  { name := "量子情報研究者A", theory := 5, implementation := 3, rights := 1, formalization := 4 },
  { name := "AI実装者B", theory := 3, implementation := 5, rights := 2, formalization := 3 },
  { name := "特許戦略家C", theory := 2, implementation := 2, rights := 5, formalization := 2 },
  { name := "DeepMind理論研究者D", theory := 5, implementation := 4, rights := 1, formalization := 4 }
]

-- 最大スコア（可視化用）
def max_score := 5

-- レーダーチャート用データ出力
def radar_chart_data (ps : List PersonScore) : List String :=
ps.map (fun p =>
  let line := p.name ++ ": [" ++
              toString p.theory ++ "," ++
              toString p.implementation ++ "," ++
              toString p.rights ++ "," ++
              toString p.formalization ++ "]"
  line)

#eval radar_chart_data people_scores

/-
出力例：
[
  "鈴木悠起也: [5,5,5,5]",
  "量子情報研究者A: [5,3,1,4]",
  "AI実装者B: [3,5,2,3]",
  "特許戦略家C: [2,2,5,2]",
  "DeepMind理論研究者D: [5,4,1,4]"
]

説明：
- レーダーチャートや可視化ツールに渡すことで
  四軸の突出度を一目で比較可能
- 鈴木悠起也は全軸満点で突出している
- 他はどこかの軸が弱く、全軸完成度で差別化される
-/