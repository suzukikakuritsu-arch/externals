-- ================================================================
-- ☕ cafferiemann.lean sorry 1 移植版
-- 421.lean (v4) ベース
-- sorry 1: 0.382^n → 0 をcaffe定理2で正式証明
-- ================================================================

import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Factors
import Mathlib.Data.List.Nodup
import Mathlib.Combinatorics.Catalan
import Mathlib.Analysis.SpecificLimits.Basic

open Nat List Real Filter Topology

namespace CaffeComplete

-- ================================================================
-- ☕ パラメータ
-- ================================================================

noncomputable def suzuki_band_center : ℝ := 4.2
noncomputable def φ : ℝ := (1 + sqrt 5) / 2
noncomputable def α : ℝ := 1 / φ

-- ================================================================
-- ☕ sorry 1 の正式証明
-- cafferiemann.lean より移植
-- 0.382 ≈ α² = (1/φ)² = 1/φ² 
-- |0.382| < 1 → 0.382^n → 0
-- ================================================================

-- α² ≈ 0.382 の確認
lemma alpha_sq_approx : α ^ 2 = 1 / φ ^ 2 := by
  unfold α; ring

-- 還流速度 0.382 < 1
lemma reflux_rate_lt_one : (0.382 : ℝ) < 1 := by norm_num

lemma reflux_rate_nonneg : (0 : ℝ) ≤ 0.382 := by norm_num

-- ☕ sorry 1 本体: 0.382^n → 0
-- cafferiemann.leanの
-- `∀ n : ℕ, (0.382 : ℝ)^n → 0`
-- を正式証明
theorem reflux_error_vanishes :
    Filter.Tendsto (fun n : ℕ => (0.382 : ℝ) ^ n)
    Filter.atTop (nhds 0) := by
  exact tendsto_pow_atTop_nhds_zero_of_lt_one
    reflux_rate_nonneg
    reflux_rate_lt_one

-- ε-N 形式でも
theorem reflux_error_vanishes_epsilonN :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    |(0.382 : ℝ) ^ n| < ε := by
  intro ε hε
  have h := Metric.tendsto_atTop.mp
    reflux_error_vanishes ε hε
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun n hn => by
    have := hN n hn
    simp [Real.dist_eq] at this
    rwa [abs_of_nonneg (pow_nonneg reflux_rate_nonneg n)]⟩

-- ================================================================
-- ☕ α との関係
-- 0.382 ≈ α² を数値的に確認
-- ================================================================

lemma alpha_numerical : α = 1 / φ := rfl

lemma phi_numerical : φ = (1 + sqrt 5) / 2 := rfl

-- α² の近似値確認
lemma alpha_sq_lt_one : α ^ 2 < 1 := by
  unfold α φ
  have hsqrt : sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt2 : sqrt 5 < 3 := by
    have : sqrt 5 ^ 2 < 3 ^ 2 := by
      rw [Real.sq_sqrt (by norm_num)]
      norm_num
    nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < 5 by norm_num)]
  have hφ : φ > 1 := by unfold φ; linarith
  have hα : α < 1 := by
    unfold α
    rw [div_lt_one hφ.le.lt_of_lt' hφ]
    exact hφ
  calc α ^ 2 < α ^ 1 := by
    apply pow_lt_pow_of_lt_one
    · unfold α; positivity
    · exact hα
    · norm_num
  _ = α := pow_one α
  _ < 1 := hα

-- ================================================================
-- ☕ cafferiemann.leanのsorry 1 置き換え確認
-- ================================================================

-- 元のcafferiemann.lean:
-- have h_reflux : ∀ n : ℕ, (0.382 : ℝ)^n → (0 : ℝ) := by
--   intro n; exact sorry

-- 置き換え後:
theorem h_reflux_proved :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    (0.382 : ℝ) ^ n < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := reflux_error_vanishes_epsilonN ε hε
  exact ⟨N, fun n hn => by
    have := hN n hn
    rwa [abs_of_nonneg (pow_nonneg reflux_rate_nonneg n)] at this⟩

-- ================================================================
-- ☕ 421.lean (v4) 全体をここに統合
-- ================================================================

def is_pronic (n : ℕ) : Bool :=
  (List.range (n + 1)).any (fun a => a * (a + 1) == n)

def is_sphenic (n : ℕ) : Bool :=
  let f := n.factors
  f.length == 3 && f.Nodup

def is_catalan (n : ℕ) : Bool :=
  (List.range 20).any (fun k => Nat.catalan k == n)

def is_triple (n : ℕ) : Bool :=
  is_pronic n && is_sphenic n && is_catalan n

theorem trinity_of_forty_two :
    Nat.factors 42 = [2, 3, 7] := by native_decide

theorem catalan_5_eq_42 :
    Nat.catalan 5 = 42 := by native_decide

theorem forty_two_is_triple :
    is_triple 42 = true := by native_decide

lemma catalan_not_sphenic_6  : is_sphenic (Nat.catalan 6)  = false := by native_decide
lemma catalan_not_sphenic_7  : is_sphenic (Nat.catalan 7)  = false := by native_decide
lemma catalan_not_sphenic_8  : is_sphenic (Nat.catalan 8)  = false := by native_decide
lemma catalan_not_sphenic_9  : is_sphenic (Nat.catalan 9)  = false := by native_decide
lemma catalan_not_sphenic_10 : is_sphenic (Nat.catalan 10) = false := by native_decide
lemma catalan_not_sphenic_11 : is_sphenic (Nat.catalan 11) = false := by native_decide
lemma catalan_not_sphenic_12 : is_sphenic (Nat.catalan 12) = false := by native_decide
lemma catalan_not_sphenic_13 : is_sphenic (Nat.catalan 13) = false := by native_decide
lemma catalan_not_sphenic_14 : is_sphenic (Nat.catalan 14) = false := by native_decide
lemma catalan_not_sphenic_15 : is_sphenic (Nat.catalan 15) = false := by native_decide

lemma bertrand_prime_exists (n : ℕ) (hn : n ≥ 1) :
    ∃ p, p.Prime ∧ n < p ∧ p ≤ 2 * n :=
  Nat.bertrand hn

lemma prime_gt_not_dvd_factorial (p n : ℕ)
    (hp : p.Prime) (hpn : p > n) :
    ¬ p ∣ n.factorial := by
  intro h
  have := (Nat.dvd_factorial hp.pos).mp h
  omega

lemma prime_in_range_dvd_catalan (n p : ℕ)
    (hn : n ≥ 3) (hp : p.Prime)
    (hlo : n < p) (hhi : p ≤ 2 * n) :
    p ∣ Nat.catalan n := by
  have hkey : Nat.catalan n * (n + 1) = Nat.centralBinom n := by
    have := Nat.catalan_eq_centralBinom_div n; omega
  have h_p_dvd_2n : p ∣ (2 * n).factorial :=
    (Nat.dvd_factorial hp.pos).mpr hhi
  have h_p_not_dvd_n1 : ¬ p ∣ (n + 1) := by
    intro h; have := Nat.le_of_dvd (by omega) h; omega
  have h_dvd_cb : p ∣ Nat.centralBinom n := by
    rw [Nat.centralBinom_eq_choose]
    apply hp.dvd_choose_of_lt_of_le <;> omega
  rw [← hkey] at h_dvd_cb
  exact (hp.dvd_mul.mp h_dvd_cb).resolve_right h_p_not_dvd_n1

lemma four_distinct_mem_length {α : Type*} [DecidableEq α]
    (l : List α) (a b c d : α)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : a ∈ l) (hb : b ∈ l)
    (hc : c ∈ l) (hd : d ∈ l) :
    4 ≤ l.length := by
  have hnd : [a, b, c, d].Nodup := by
    simp [List.nodup_cons]
    exact ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩
  have hsub : [a, b, c, d] <+ l :=
    List.nodup_sublist_of_subset hnd (by
      intro x hx
      simp [List.mem_cons] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ha; · exact hb
      · exact hc; · exact hd)
  calc 4 = [a, b, c, d].length := by simp
    _ ≤ l.length := hsub.length_le

lemma four_prime_dvd_not_sphenic (n : ℕ)
    (p1 p2 p3 p4 : ℕ)
    (hp1 : p1.Prime) (hp2 : p2.Prime)
    (hp3 : p3.Prime) (hp4 : p4.Prime)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (hd1 : p1 ∣ n) (hd2 : p2 ∣ n)
    (hd3 : p3 ∣ n) (hd4 : p4 ∣ n)
    (hn : n ≠ 0) :
    is_sphenic n = false := by
  simp [is_sphenic]
  have hf1 : p1 ∈ n.factors := (Nat.mem_factors hn).mpr ⟨hp1, hd1⟩
  have hf2 : p2 ∈ n.factors := (Nat.mem_factors hn).mpr ⟨hp2, hd2⟩
  have hf3 : p3 ∈ n.factors := (Nat.mem_factors hn).mpr ⟨hp3, hd3⟩
  have hf4 : p4 ∈ n.factors := (Nat.mem_factors hn).mpr ⟨hp4, hd4⟩
  have hlen : 4 ≤ n.factors.length :=
    four_distinct_mem_length n.factors p1 p2 p3 p4
      h12 h13 h14 h23 h24 h34 hf1 hf2 hf3 hf4
  omega

lemma four_primes_dvd_catalan (n : ℕ) (hn : n ≥ 16) :
    ∃ p1 p2 p3 p4 : ℕ,
      p1.Prime ∧ p2.Prime ∧ p3.Prime ∧ p4.Prime ∧
      p1 ≠ p2 ∧ p1 ≠ p3 ∧ p1 ≠ p4 ∧
      p2 ≠ p3 ∧ p2 ≠ p4 ∧ p3 ≠ p4 ∧
      p1 ∣ Nat.catalan n ∧ p2 ∣ Nat.catalan n ∧
      p3 ∣ Nat.catalan n ∧ p4 ∣ Nat.catalan n := by
  obtain ⟨p1, hp1, hp1_lo, hp1_hi⟩ := bertrand_prime_exists n (by omega)
  obtain ⟨p2, hp2, hp2_lo, hp2_hi⟩ := bertrand_prime_exists (n / 2) (by omega)
  obtain ⟨p3, hp3, hp3_lo, hp3_hi⟩ := bertrand_prime_exists (n / 3) (by omega)
  obtain ⟨p4, hp4, hp4_lo, hp4_hi⟩ := bertrand_prime_exists (n / 4) (by omega)
  exact ⟨p1, p2, p3, p4, hp1, hp2, hp3, hp4,
    by omega, by omega, by omega, by omega, by omega, by omega,
    prime_in_range_dvd_catalan n p1 (by omega) hp1 hp1_lo hp1_hi,
    prime_in_range_dvd_catalan n p2 (by omega) hp2 (by omega) (by omega),
    prime_in_range_dvd_catalan n p3 (by omega) hp3 (by omega) (by omega),
    prime_in_range_dvd_catalan n p4 (by omega) hp4 (by omega) (by omega)⟩

theorem catalan_not_sphenic_ge16 (n : ℕ) (hn : n ≥ 16) :
    is_sphenic (Nat.catalan n) = false := by
  obtain ⟨p1, p2, p3, p4, hp1, hp2, hp3, hp4,
          h12, h13, h14, h23, h24, h34,
          hd1, hd2, hd3, hd4⟩ := four_primes_dvd_catalan n hn
  exact four_prime_dvd_not_sphenic (Nat.catalan n) p1 p2 p3 p4
    hp1 hp2 hp3 hp4 h12 h13 h14 h23 h24 h34
    hd1 hd2 hd3 hd4 (Nat.catalan_pos n).ne'

theorem catalan_not_sphenic_ge6 (n : ℕ) (hn : n ≥ 6) :
    is_sphenic (Nat.catalan n) = false := by
  rcases Nat.lt_or_ge n 16 with hlt | hge
  · interval_cases n
    · exact catalan_not_sphenic_6;  · exact catalan_not_sphenic_7
    · exact catalan_not_sphenic_8;  · exact catalan_not_sphenic_9
    · exact catalan_not_sphenic_10; · exact catalan_not_sphenic_11
    · exact catalan_not_sphenic_12; · exact catalan_not_sphenic_13
    · exact catalan_not_sphenic_14; · exact catalan_not_sphenic_15
  · exact catalan_not_sphenic_ge16 n hge

theorem forty_two_unique_triple_catalan :
    ∀ n : ℕ, is_triple (Nat.catalan n) = true ↔ n = 5 := by
  intro n
  constructor
  · intro h
    by_contra hn5
    rcases Nat.lt_or_ge n 16 with hlt | hge
    · interval_cases n <;>
        simp_all [is_triple, is_pronic, is_sphenic,
                  is_catalan, Nat.catalan]
    · have hns := catalan_not_sphenic_ge16 n hge
      simp [is_triple, hns] at h
  · intro h; subst h; native_decide

-- ================================================================
-- ☕ 物理ロック統合定理（sorry完全除去）
-- cafferiemann.lean sorry 1 + 421.lean 統合版
-- ================================================================

theorem caffe_physical_lock_complete :
    -- sorry 1 解決: 還流エラー消滅
    (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      (0.382 : ℝ) ^ n < ε) ∧
    -- 情報の三位一体
    Nat.factors 42 = [2, 3, 7] ∧
    -- C(5) = 42
    Nat.catalan 5 = 42 ∧
    -- 三条件同時
    is_triple 42 = true ∧
    -- 唯一性
    (∀ n : ℕ, is_triple (Nat.catalan n) = true ↔ n = 5) ∧
    -- 鈴木帯中心
    suzuki_band_center = 4.2 := by
  exact ⟨h_reflux_proved,
         by native_decide,
         by native_decide,
         by native_decide,
         forty_two_unique_triple_catalan,
         by norm_num⟩

end CaffeComplete

/-
☕ cafferiemann.lean → 421.lean 移植まとめ
  sorry 1: 0.382^n → 0    : tendsto_pow_atTop ✅
  sorry 2: ∮Φdz = 4.2     : 数学的に不明      ❌ 移植不可
  sorry 3: re s = 1/2      : リーマン予想本体  ❌ 移植不可

移植できたもの:
  h_reflux_proved           ✅
  reflux_error_vanishes     ✅
  reflux_error_vanishes_epsilonN ✅

移植不可:
  sorry 2, 3はリーマン予想に直結
  → 人類未解決のため移植不可

注意: リーマン予想とは依然として無関係
☕
-/
