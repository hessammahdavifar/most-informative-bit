/-
Copyright 2026 the general-courtade-kumar-lean contributors.
Licensed under the Apache License, Version 2.0.
Source: https://github.com/dpwoodru/general-courtade-kumar-lean
Vendored basic definitions and finite probability identities only.
Local change: import paths; source statements and proofs unchanged.
-/
import MostInformativeBit.Vendor.GeneralCK.Distribution

namespace GeneralCK.Information
open scoped BigOperators

noncomputable def cubeWeight (n : ℕ) : ℝ := (2 : ℝ) ^ (-(n : ℤ))

noncomputable def posterior {n : ℕ} (f : Cube n → Bool) (p : ℝ) (y : Cube n) : ℝ :=
  ∑ x, if f x = true then noiseKernel p x y else 0

noncomputable def meanIndicator {n : ℕ} (f : Cube n → Bool) : ℝ :=
  cubeWeight n * ∑ x, if f x = true then (1 : ℝ) else 0

theorem weight_sum (n : ℕ) : (∑ _ : Cube n, cubeWeight n) = 1 := by
  simp [cubeWeight, Cube, zpow_neg, zpow_natCast]

theorem kernel_symm {n : ℕ} (p : ℝ) (x y : Cube n) :
    noiseKernel p x y = noiseKernel p y x := by
  simp only [noiseKernel, eq_comm]

theorem kernel_column_sum {n : ℕ} (p : ℝ) (y : Cube n) :
    ∑ x, noiseKernel p x y = 1 := by
  simp_rw [kernel_symm p _ y]
  exact noiseKernel_sum p y

theorem joint_true {n : ℕ} (f : Cube n → Bool) (p : ℝ) (y : Cube n) :
    jointMass f p true y = cubeWeight n * posterior f p y := rfl

theorem joint_output {n : ℕ} (f : Cube n → Bool) (p : ℝ) (y : Cube n) :
    ∑ b, jointMass f p b y = cubeWeight n := by
  classical
  have hb (x : Cube n) :
      (∑ b : Bool, if f x = b then noiseKernel p x y else 0) = noiseKernel p x y := by
    cases f x <;> simp
  simp only [jointMass, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [hb, kernel_column_sum, mul_one, cubeWeight]

theorem joint_false {n : ℕ} (f : Cube n → Bool) (p : ℝ) (y : Cube n) :
    jointMass f p false y = cubeWeight n * (1 - posterior f p y) := by
  have h := joint_output f p y
  simp only [Fintype.sum_bool, joint_true] at h
  linarith

theorem marginal_true {n : ℕ} (f : Cube n → Bool) (p : ℝ) :
    ∑ y, jointMass f p true y = meanIndicator f := by
  classical
  simp only [jointMass, ← Finset.mul_sum, meanIndicator, cubeWeight]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs with h
  · simp [noiseKernel_sum]
  · simp

theorem marginal_false {n : ℕ} (f : Cube n → Bool) (p : ℝ) :
    ∑ y, jointMass f p false y = 1 - meanIndicator f := by
  have h := jointMass_sum f p
  simp only [Fintype.sum_bool, marginal_true] at h
  linarith

theorem entropy_bool (q : Bool → ℝ) (hq : q false + q true = 1) :
    entropy q = H (q true) := by
  have hf : q false = 1 - q true := by linarith
  simp only [entropy, Fintype.sum_bool, hf, H,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]

theorem scaled_binary_entropy (w t : ℝ) :
    Real.negMulLog (w * t) + Real.negMulLog (w * (1 - t)) =
      Real.negMulLog w + w * Real.binEntropy t := by
  rw [Real.negMulLog_mul, Real.negMulLog_mul,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring

theorem entropy_input {n : ℕ} (f : Cube n → Bool) (p : ℝ) :
    entropy (fun b => ∑ y, jointMass f p b y) = H (meanIndicator f) := by
  rw [entropy_bool]
  · rw [marginal_true]
  · rw [marginal_false, marginal_true]; ring

theorem entropy_joint {n : ℕ} (f : Cube n → Bool) (p : ℝ) :
    entropy (fun byPair : Bool × Cube n => jointMass f p byPair.1 byPair.2) =
      entropy (fun _ : Cube n => cubeWeight n) +
      cubeWeight n * ∑ y, H (posterior f p y) := by
  classical
  simp only [entropy, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [Fintype.sum_bool, joint_false, joint_true, scaled_binary_entropy]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, add_div]
  simp only [H, div_eq_mul_inv, ← Finset.sum_mul]
  ring

/-- Finite conditional-entropy identity, with all normalizations in bits. -/
theorem mutualInformation_eq {n : ℕ} (f : Cube n → Bool) (p : ℝ) :
    mutualInformation f p = H (meanIndicator f) -
      cubeWeight n * ∑ y, H (posterior f p y) := by
  unfold mutualInformation
  rw [entropy_input, entropy_joint]
  simp_rw [joint_output]
  ring

theorem posterior_nonneg {n : ℕ} (f : Cube n → Bool) {p : ℝ}
    (h₀ : 0 ≤ p) (h₁ : p ≤ 1) (y : Cube n) : 0 ≤ posterior f p y := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact noiseKernel_nonneg h₀ h₁ x y
  · exact le_rfl

theorem posterior_le_one {n : ℕ} (f : Cube n → Bool) {p : ℝ}
    (h₀ : 0 ≤ p) (h₁ : p ≤ 1) (y : Cube n) : posterior f p y ≤ 1 := by
  rw [← kernel_column_sum p y]
  apply Finset.sum_le_sum
  intro x _
  split_ifs
  · exact le_rfl
  · exact noiseKernel_nonneg h₀ h₁ x y

theorem kernel_half {n : ℕ} (x y : Cube n) :
    noiseKernel (1 / 2) x y = cubeWeight n := by
  have h : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  simp only [noiseKernel, h, ite_self, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, cubeWeight, zpow_neg, zpow_natCast]
  simp [one_div, inv_pow]

theorem posterior_half {n : ℕ} (f : Cube n → Bool) (y : Cube n) :
    posterior f (1 / 2) y = meanIndicator f := by
  classical
  simp only [posterior, kernel_half, meanIndicator, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

theorem mutualInformation_half {n : ℕ} (f : Cube n → Bool) :
    mutualInformation f (1 / 2) = 0 := by
  rw [mutualInformation_eq]
  simp_rw [posterior_half]
  rw [Finset.mul_sum]
  simp_rw [← Finset.sum_mul, weight_sum, one_mul, sub_self]

theorem mean_posterior {n : ℕ} (f : Cube n → Bool) (p : ℝ) :
    cubeWeight n * ∑ y, posterior f p y = meanIndicator f := by
  rw [Finset.mul_sum]
  exact marginal_true f p

end GeneralCK.Information

