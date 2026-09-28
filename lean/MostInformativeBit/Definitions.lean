import MostInformativeBit.Vendor.GeneralCK.InformationIdentity
import Mathlib.Tactic

namespace MostInformativeBit
open scoped BigOperators

abbrev Cube := GeneralCK.Cube

/-- Entropy in natural units, in the paper's sign-mean parametrization. -/
noncomputable def h (m : ℝ) : ℝ := Real.binEntropy ((1-m)/2)

noncomputable def phi (r : ℝ) : ℝ := Real.log 2 - h r

/-- BSC mutual information in natural units, using finite joint and marginal masses. -/
noncomputable def information {n : ℕ} (f : Cube n → Bool) (r : ℝ) : ℝ :=
  Real.log 2 * GeneralCK.mutualInformation f ((1-r)/2)

noncomputable def gap {n : ℕ} (f : Cube n → Bool) (r : ℝ) : ℝ :=
  information f r - phi r

/-- The requested main theorem, as a target proposition. This is not an assertion. -/
def MainTheorem : Prop := ∀ n (f : Cube n → Bool) (r : ℝ),
  0 ≤ r → r ≤ 1 → information f r ≤ phi r

theorem phi_nonneg (r : ℝ) : 0 ≤ phi r := by
  unfold phi h
  exact sub_nonneg.mpr Real.binEntropy_le_log_two

theorem phi_zero : phi 0 = 0 := by simp [phi, h, one_div]

theorem information_zero {n : ℕ} (f : Cube n → Bool) : information f 0 = 0 := by
  unfold information
  rw [show (1-(0:ℝ))/2 = 1/2 by norm_num,
    GeneralCK.Information.mutualInformation_half]
  ring

theorem gap_zero {n : ℕ} (f : Cube n → Bool) : gap f 0 = 0 := by
  simp [gap, information_zero, phi_zero]

theorem information_eq_conditional_entropy {n : ℕ} (f : Cube n → Bool) (r : ℝ) :
    information f r = Real.binEntropy (GeneralCK.Information.meanIndicator f) -
      GeneralCK.Information.cubeWeight n *
        ∑ y, Real.binEntropy (GeneralCK.Information.posterior f ((1-r)/2) y) := by
  unfold information
  rw [GeneralCK.Information.mutualInformation_eq]
  unfold GeneralCK.H
  rw [← Finset.sum_div]
  have hn : Real.log 2 ≠ 0 := ne_of_gt GeneralCK.log_two_pos
  field_simp
  <;> ring

/-- Explicit relation to the usual formulation in bits. -/
theorem information_le_phi_iff {n : ℕ} (f : Cube n → Bool) (r : ℝ) :
    information f r ≤ phi r ↔
      GeneralCK.mutualInformation f ((1-r)/2) ≤ 1-GeneralCK.H ((1-r)/2) := by
  unfold information phi h GeneralCK.H
  have hn := GeneralCK.log_two_pos
  rw [← le_div_iff₀' hn]
  congr 1
  field_simp

end MostInformativeBit
