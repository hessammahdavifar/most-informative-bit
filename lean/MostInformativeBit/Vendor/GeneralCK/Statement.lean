/-
Copyright 2026 the general-courtade-kumar-lean contributors.
Licensed under the Apache License, Version 2.0.
Source: https://github.com/dpwoodru/general-courtade-kumar-lean
Vendored basic definitions and finite probability identities only.
Local change: import paths; source statements and proofs unchanged.
-/
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Precise target, not a proof of the Courtade--Kumar conjecture. -/
namespace GeneralCK
open scoped BigOperators

abbrev Cube (n : ℕ) := Fin n → Bool

/-- Binary entropy in bits, including the continuous endpoint values. -/
noncomputable def H (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2

/-- Independent coordinate bit flips. `p` is crossover, not correlation. -/
noncomputable def noiseKernel {n : ℕ} (p : ℝ) (x y : Cube n) : ℝ :=
  ∏ i, if x i = y i then 1 - p else p

/-- The joint mass of `(f(X),Y)` for uniform `X` and binary symmetric noise. -/
noncomputable def jointMass {n : ℕ} (f : Cube n → Bool) (p : ℝ)
    (b : Bool) (y : Cube n) : ℝ :=
  (2 : ℝ) ^ (-(n : ℤ)) * ∑ x, if f x = b then noiseKernel p x y else 0

/-- Finite Shannon entropy in bits. Used below only for probability masses. -/
noncomputable def entropy {α : Type*} [Fintype α] (q : α → ℝ) : ℝ :=
  (∑ a, Real.negMulLog (q a)) / Real.log 2

/-- Mutual information from joint and marginal finite masses. -/
noncomputable def mutualInformation {n : ℕ} (f : Cube n → Bool) (p : ℝ) : ℝ :=
  entropy (fun b => ∑ y, jointMass f p b y) +
  entropy (fun y => ∑ b, jointMass f p b y) -
  entropy (fun byPair : Bool × Cube n => jointMass f p byPair.1 byPair.2)

/-- Review target: all dimensions (including zero), all Boolean functions,
all crossover probabilities (including zero, one half, and one).
This is a proposition definition, not an asserted theorem. -/
def GeneralCourtadeKumar : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ),
    0 ≤ p → p ≤ 1 → mutualInformation f p ≤ 1 - H p

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

@[simp] theorem H_zero : H 0 = 0 := by simp [H]
@[simp] theorem H_one : H 1 = 0 := by simp [H]
@[simp] theorem H_half : H (1 / 2) = 1 := by
  have h : Real.log 2 ≠ 0 := ne_of_gt log_two_pos
  simpa [H, one_div] using div_self h

theorem H_complement (p : ℝ) : H (1 - p) = H p := by simp [H]

theorem H_nonneg {p : ℝ} (h₀ : 0 ≤ p) (h₁ : p ≤ 1) : 0 ≤ H p :=
  div_nonneg (Real.binEntropy_nonneg h₀ h₁) log_two_pos.le

theorem H_le_one (p : ℝ) : H p ≤ 1 := by
  rw [H, div_le_one log_two_pos]
  exact Real.binEntropy_le_log_two

theorem H_continuous : Continuous H :=
  Real.binEntropy_continuous.div_const _

end GeneralCK
