import MostInformativeBit.ProbabilityEndpoints
import MostInformativeBit.MaximumPrinciple

namespace MostInformativeBit

/-- Precise remaining analytic claim, matching the manuscript's coverage lemma.
This is a proposition definition, not an axiom or an asserted theorem.
-/
def PositiveGapGrowth : Prop :=
  ∀ n (f : Cube n → Bool) (r : ℝ),
    0 < r → r < 1 → 0 < gap f r → 0 < deriv (gap f) r

/-- The final theorem follows from growth of positive gaps.
This checked reduction still requires the substantive growth theorem.
-/
theorem main_of_positive_gap_growth (growth : PositiveGapGrowth) : MainTheorem := by
  intro n f r hr0 hr1
  have hh := nonpositive_of_positive_derivative_on_positive_set
    (gap_continuous f).continuousOn (le_of_eq (gap_zero f))
    (gap_one_nonpos f) (fun x hx hp => growth n f x hx.1 hx.2 hp)
    r ⟨hr0, hr1⟩
  exact sub_nonpos.mp hh

/-- The sorting lemma's information-dominance conclusion. -/
def SortingDominance : Prop :=
  ∀ n (f : Cube n → Bool), ∃ g : Cube n → Bool,
    Monotone g ∧ ∀ r ∈ Set.Icc (0:ℝ) 1, information f r ≤ information g r

/-- The precise monotone-function version of the coverage lemma. -/
def MonotoneGapGrowth : Prop :=
  ∀ n (f : Cube n → Bool), Monotone f →
    ∀ r ∈ Set.Ioo (0:ℝ) 1, 0 < gap f r → 0 < deriv (gap f) r

/-- The manuscript's final argument, with its two substantive inputs explicit. -/
theorem main_of_sorting_and_monotone_growth
    (sorting : SortingDominance) (growth : MonotoneGapGrowth) : MainTheorem := by
  intro n f r hr0 hr1
  obtain ⟨g, hgm, hgi⟩ := sorting n f
  have hh := nonpositive_of_positive_derivative_on_positive_set
    (gap_continuous g).continuousOn (le_of_eq (gap_zero g))
    (gap_one_nonpos g) (growth n g hgm) r ⟨hr0, hr1⟩
  exact le_trans (hgi r ⟨hr0, hr1⟩) (sub_nonpos.mp hh)

end MostInformativeBit
