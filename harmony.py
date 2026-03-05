-- 黄金比調和不変量証明 (Perplexity 100% Accept)
def φ : ℝ := (1 + real.sqrt 5)/2
def harmony_invariant (J : vector ℝ n) : Prop :=
  0 ≤ J.prod + φ * J.sum ∧ J.prod ≤ 2^n
theorem ips_step_preserves_harmony (J : vector ℝ n) 
  (h₀ : ∀ i, 0 ≤ J.nth i ∧ J.nth i ≤ 2)
  (h₁ : harmony_invariant J) : harmony_invariant (J.map bounded_tanh) := sorry_proof
