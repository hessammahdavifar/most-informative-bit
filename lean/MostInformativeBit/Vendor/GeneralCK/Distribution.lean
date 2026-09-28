/-
Copyright 2026 the general-courtade-kumar-lean contributors.
Licensed under the Apache License, Version 2.0.
Source: https://github.com/dpwoodru/general-courtade-kumar-lean
Vendored basic definitions and finite probability identities only.
Local change: import paths; source statements and proofs unchanged.
-/
import MostInformativeBit.Vendor.GeneralCK.Statement

namespace GeneralCK
open scoped BigOperators

theorem noiseKernel_nonneg {n : ℕ} {p : ℝ} (h₀ : 0 ≤ p) (h₁ : p ≤ 1)
    (x y : Cube n) : 0 ≤ noiseKernel p x y := by
  unfold noiseKernel
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith

/-- Exact normalization of the independently flipped output coordinates. -/
theorem noiseKernel_sum {n : ℕ} (p : ℝ) (x : Cube n) :
    ∑ y, noiseKernel p x y = 1 := by
  classical
  have h := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset Bool))
    (fun i b => if x i = b then 1 - p else p)
  have hb (i : Fin n) : (∑ b : Bool, if x i = b then 1 - p else p) = 1 := by
    cases x i <;> simp
  simpa only [noiseKernel, Fintype.piFinset_univ, hb, Finset.prod_const_one] using h.symm

theorem jointMass_nonneg {n : ℕ} (f : Cube n → Bool) {p : ℝ}
    (h₀ : 0 ≤ p) (h₁ : p ≤ 1) (b : Bool) (y : Cube n) :
    0 ≤ jointMass f p b y := by
  unfold jointMass
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact noiseKernel_nonneg h₀ h₁ x y
  · exact le_rfl

theorem jointMass_sum {n : ℕ} (f : Cube n → Bool) (p : ℝ) :
    ∑ b, ∑ y, jointMass f p b y = 1 := by
  classical
  have hb (x y : Cube n) :
      (∑ b : Bool, if f x = b then noiseKernel p x y else 0) = noiseKernel p x y := by
    cases f x <;> simp
  simp only [jointMass, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; arg 2; ext y; rw [Finset.sum_comm]
  simp only [hb]
  rw [Finset.sum_comm]
  simp [noiseKernel_sum, Cube, zpow_neg, zpow_natCast]

end GeneralCK
