import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
open Real

/-
Golden Ratio
-/

def φ : ℝ := (1 + sqrt 5) / 2

theorem phi_identity : φ^2 = φ + 1 := by
  unfold φ
  ring_nf
  field_simp
  ring

/-
GER state
-/

structure GERState where
  G : ℝ
  E : ℝ

variable (a b : ℝ)

/-
GER dynamics
-/

def GER_step (s : GERState) : GERState :=
{
  G := a * s.G + φ * (1 - a) * s.E,
  E := b * (s.E + log (1 + (a * s.G + φ * (1 - a) * s.E)))
}

/-
Fixed point
-/

def FixedPoint (s : GERState) : Prop :=
GER_step a b s = s

/-
Core theorem
G/E = φ
-/

theorem GER_ratio
  (G E a : ℝ)
  (h : G = a*G + φ*(1-a)*E)
  (ha : a ≠ 1)
  (hE : E ≠ 0)
  :
  G/E = φ := by

  have h1 : G - a*G = φ*(1-a)*E := by linarith

  have h2 : G*(1-a) = φ*(1-a)*E := by
    ring_nf at h1
    simpa using h1

  have h3 : G = φ*E := by
    have h4 : (1-a) ≠ 0 := by
      exact sub_ne_zero.mpr ha
    have := mul_right_cancel₀ h4 h2
    simpa using this

  field_simp [h3]

/-
Stationary equation
-/

def stationary (G : ℝ) : Prop :=
G = φ * log (1 + G)

theorem stationary_equiv
  (G : ℝ)
  (h : stationary G)
  (hpos : log (1 + G) ≠ 0) :
  G / log (1 + G) = φ := by
  unfold stationary at h
  field_simp [h, hpos]
