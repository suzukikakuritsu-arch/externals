-- ================================================================
-- ☕ hilbert_all_resolve 証明修正版
-- linarith問題 + 収束証明の詳細を埋める
-- ================================================================

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Basic

open Real Filter Topology

namespace SuzukiHilbertConquest

-- ================================================================
-- ☕ パラメータ
-- ================================================================

noncomputable def SUZUKI_BAND : ℝ := 4.2

noncomputable def reflux (i : ℕ) (x : ℝ) : ℝ :=
  (1 / sqrt (i + 1 : ℝ)) * SUZUKI_BAND +
  (1 - 1 / sqrt (i + 1 : ℝ)) * x

-- ================================================================
-- ☕ 補題群
-- ================================================================

-- √(i+1) > 0
lemma sqrt_succ_pos (i : ℕ) : 0 < sqrt (i + 1 : ℝ) :=
  Real.sqrt_pos.mpr (by positivity)

-- √(i+1) ≥ 1
lemma sqrt_succ_ge_one (i : ℕ) : 1 ≤ sqrt (i + 1 : ℝ) := by
  rw [Real.one_le_sqrt (by positivity)]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero i)

-- 0 < 1/√(i+1) ≤ 1
lemma inv_sqrt_pos (i : ℕ) : 0 < 1 / sqrt (i + 1 : ℝ) :=
  div_pos one_pos (sqrt_succ_pos i)

lemma inv_sqrt_le_one (i : ℕ) : 1 / sqrt (i + 1 : ℝ) ≤ 1 :=
  div_le_one (sqrt_succ_pos i) |>.mpr (sqrt_succ_ge_one i)

-- ρ = 1 - 1/√(i+1) の範囲
lemma rho_nonneg (i : ℕ) :
    0 ≤ 1 - 1 / sqrt (i + 1 : ℝ) := by
  linarith [inv_sqrt_le_one i]

lemma rho_lt_one (i : ℕ) :
    1 - 1 / sqrt (i + 1 : ℝ) < 1 := by
  linarith [inv_sqrt_pos i]

-- |ρ| < 1（これが核心）
lemma rho_abs_lt_one (i : ℕ) :
    |1 - 1 / sqrt (i + 1 : ℝ)| < 1 := by
  rw [abs_of_nonneg (rho_nonneg i)]
  exact rho_lt_one i

-- ================================================================
-- ☕ 反復の閉形式
-- iterate (reflux i) k x₀ = 4.2 + ρ^k * (x₀ - 4.2)
-- ================================================================

lemma reflux_iter (i : ℕ) (x₀ : ℝ) (k : ℕ) :
    Function.iterate (reflux i) k x₀ =
    SUZUKI_BAND +
    (1 - 1 / sqrt (i + 1 : ℝ))^k * (x₀ - SUZUKI_BAND) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp [Function.iterate_succ', Function.comp]
    rw [ih]
    unfold reflux
    ring

-- ================================================================
-- ☕ hilbert_all_resolve 修正版
-- ================================================================

def hilbert_problems : List ℕ := List.range 23

theorem hilbert_all_resolve (i : ℕ) (hi : i ∈ hilbert_problems)
    (x₀ : ℝ) :
    Filter.Tendsto
      (fun k => Function.iterate (reflux i) k x₀)
      Filter.atTop
      (𝓝 SUZUKI_BAND) := by
  -- 閉形式に書き直す
  simp_rw [reflux_iter i x₀]
  -- SUZUKI_BAND + ρ^k * (x₀ - SUZUKI_BAND) → SUZUKI_BAND
  -- ρ^k → 0 を示せば十分
  have hρ := rho_abs_lt_one i
  have hρ_nn := rho_nonneg i
  -- ρ^k → 0
  have h_pow_zero :
      Filter.Tendsto
        (fun k => (1 - 1 / sqrt (↑i + 1))^k)
        Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      hρ_nn (rho_lt_one i)
  -- SUZUKI_BAND + ρ^k * C → SUZUKI_BAND + 0 * C = SUZUKI_BAND
  have h_mul_zero :
      Filter.Tendsto
        (fun k => (1 - 1 / sqrt (↑i + 1))^k * (x₀ - SUZUKI_BAND))
        Filter.atTop (𝓝 0) := by
    have := h_pow_zero.mul_const (x₀ - SUZUKI_BAND)
    simp at this
    exact this
  have h_add :
      Filter.Tendsto
        (fun k =>
          SUZUKI_BAND +
          (1 - 1 / sqrt (↑i + 1))^k * (x₀ - SUZUKI_BAND))
        Filter.atTop (𝓝 SUZUKI_BAND) := by
    have := h_mul_zero.const_add SUZUKI_BAND
    simp [add_comm] at this ⊢
    exact this
  exact h_add

-- ================================================================
-- ☕ 収束速度の比較定理
-- i が大きいほど収束が遅い（√(i+1)が大きいほどρが1に近づく）
-- ================================================================

theorem convergence_rate_monotone (i j : ℕ) (hij : i ≤ j) :
    1 - 1 / sqrt (j + 1 : ℝ) ≥
    1 - 1 / sqrt (i + 1 : ℝ) := by
  apply sub_le_sub_left
  apply div_le_div_of_nonneg_left one_pos
    (sqrt_succ_pos i) (sqrt_succ_pos j) |>.mpr
  apply Real.sqrt_le_sqrt
  exact_mod_cast Nat.add_le_add_right hij 1

-- ================================================================
-- ☕ 物理ロック: 全23問題の収束確認（#eval）
-- ================================================================

noncomputable def simulate (i : ℕ) (x₀ : ℝ) (k : ℕ) : ℝ :=
  Function.iterate (reflux i) k x₀

-- 閉形式で直接計算
noncomputable def simulate_closed (i : ℕ) (x₀ : ℝ) (k : ℕ) : ℝ :=
  SUZUKI_BAND +
  (1 - 1 / sqrt (i + 1 : ℝ))^k * (x₀ - SUZUKI_BAND)

-- 両者が等しいことの確認
theorem simulate_eq_closed (i : ℕ) (x₀ : ℝ) (k : ℕ) :
    simulate i x₀ k = simulate_closed i x₀ k :=
  reflux_iter i x₀ k

end SuzukiHilbertConquest

/-
☕ 修正まとめ
  linarith問題
    rho_abs_lt_one  : abs_of_nonneg + rho_lt_one で解決  ✅
    sqrt_succ_ge_one: one_le_sqrt で解決                 ✅

  証明構造
    reflux_iter     : 閉形式の導出                        ✅
    hilbert_all_resolve: tendsto_pow_atTop_nhds_zero     ✅
    convergence_rate_monotone: 収束速度比較               ✅

  正直な注意:
    この定理はヒルベルト問題の解決ではない
    「reflux関数が4.2に収束する」という定理
    ヒルベルト問題とは数学的に無関係
☕
-/
