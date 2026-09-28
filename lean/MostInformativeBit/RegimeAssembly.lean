import MostInformativeBit.MainReduction
import MostInformativeBit.MonotoneReduction
import MostInformativeBit.EntropyFlow

namespace MostInformativeBit

/-- The sorting input to the maximum-principle reduction is fully discharged. -/
theorem sorting_dominance : SortingDominance := by
  intro n f
  obtain ⟨g, hg, _, hdom⟩ := monotoneReduction f
  exact ⟨g, hg, fun r hr => hdom r hr.1 hr.2⟩

theorem information_constant {n : ℕ} (b : Bool) (r : ℝ) :
    information (fun _ : Cube n => b) r = 0 := by
  rw [information_eq_phiEntropy]
  change phiEntropy (noise r (fun _ : Cube n => cubeSign b)) = 0
  simp only [noise_const, phiEntropy, cubeExpect_const, sub_self]

theorem nonconstant_of_positive_gap {n : ℕ} {f : Cube n → Bool} {r : ℝ}
    (hp : 0 < gap f r) : ∃ x y, f x ≠ f y := by
  by_contra hn
  push Not at hn
  let x₀ : Cube n := fun _ => false
  have he : f = fun _ => f x₀ := funext fun x => hn x x₀
  rw [he, gap, information_constant] at hp
  linarith [phi_nonneg r]

theorem gap_hasDerivAt {n : ℕ} {f : Cube n → Bool} {r : ℝ}
    (hf : ∃ x y, f x ≠ f y) (hr0 : 0 < r) (hr1 : r < 1) :
    HasDerivAt (gap f)
      (entropyAction (noise r (signField f))/r-Real.artanh r) r := by
  have hd := phiEntropy_noise_hasDerivAt (signField f) (ne_of_gt hr0)
    (noise_signField_mem_Ioo (by linarith) hr1 hf)
  have he : information f = fun t => phiEntropy (noise t (signField f)) :=
    funext (information_eq_phiEntropy f)
  rw [← he] at hd
  exact hd.sub (phi_hasDerivAt (by linarith) hr1)

theorem positive_gap_derivative_of_action {n : ℕ} {f : Cube n → Bool} {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hp : 0 < gap f r)
    (ha : r*Real.artanh r < entropyAction (noise r (signField f))) :
    0 < deriv (gap f) r := by
  rw [(gap_hasDerivAt (nonconstant_of_positive_gap hp) hr0 hr1).deriv]
  exact sub_pos.mpr ((lt_div_iff₀ hr0).mpr (by simpa only [mul_comm] using ha))

/-- A precise remaining growth obligation in the action normalization of the manuscript.
This is a proposition definition, not a proof of the channel regimes. -/
def MonotoneActionGrowth : Prop :=
  ∀ n (f : Cube n → Bool), Monotone f →
    ∀ r ∈ Set.Ioo (0:ℝ) 1, 0 < gap f r →
      r*Real.artanh r < entropyAction (noise r (signField f))

/-- Full final assembly, conditional only on the remaining monotone action-growth theorem. -/
theorem main_of_monotone_action_growth (hg : MonotoneActionGrowth) : MainTheorem := by
  apply main_of_sorting_and_monotone_growth sorting_dominance
  intro n f hf r hr hp
  exact positive_gap_derivative_of_action hr.1 hr.2 hp (hg n f hf r hr hp)

end MostInformativeBit
