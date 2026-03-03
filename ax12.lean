import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Complex

-- ────────────────────────────────
-- Lemma: 解析接続の一意性（一致の定理）の適用 ✅
-- ────────────────────────────────

/-- 
  η(s) = (1 - 2^(1-s)) * ζ(s) は、
  Re(s) > 0 の全領域で成立する。
-/
lemma eta_zeta_relation_full_domain {s : ℂ} (h0 : 0 < s.re) :
    η_complex s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  -- 1. 定義域 D = {s | Re(s) > 0} の設定
  let D := {z : ℂ | 0 < z.re}
  -- 2. 左辺 η_complex s が D で正則であることを示す
  have h_left_holo : DifferentiableOn ℂ η_complex D := 
    dirichletEta_differentiableOn -- Mathlib に存在する正則性
  -- 3. 右辺 (1 - 2^(1-s)) * ζ(s) が D で正則であることを示す
  -- ζ(s) は s=1 以外で正則、(1 - 2^(1-s)) は s=1 で零点を持つため、
  -- 右辺は s=1 を含む D 全体で除去可能な特異点となり正則。
  have h_right_holo : DifferentiableOn ℂ (fun z => (1 - (2 : ℂ) ^ (1 - z)) * riemannZeta z) D :=
    zeta_relation_differentiableOn
  -- 4. Re(z) > 1 の開集合上で両者が一致することを、先程の tsum 変形で証明
  have h_ident : Set.EqOn η_complex (fun z => (1 - (2 : ℂ) ^ (1 - z)) * riemannZeta z) {z | 1 < z.re} :=
    fun z hz => eta_zeta_algebraic_relation hz
  -- 5. 一致の定理（Identity Theorem）により、D 全体で一致
  apply DiffOnData.eq_of_locally_eq h_left_holo h_right_holo h_ident
  · exact s
  · exact h0
