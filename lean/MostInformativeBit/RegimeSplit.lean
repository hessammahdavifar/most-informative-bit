import MostInformativeBit.LowRegime
import MostInformativeBit.MiddleGrowth

namespace MostInformativeBit

/-- The remaining high-correlation action estimate. This definition does not
assert its proof. The low and middle regimes are discharged below. -/
def HighActionGrowth : Prop :=
  ∀ n (f : Cube n → Bool), Monotone f → ∀ ell : ℝ, 7/2 ≤ ell →
    0 < gap f (Real.tanh ell) →
    Real.tanh ell*ell < entropyAction (noise (Real.tanh ell) (signField f))

/-- Final regime split, conditional only on the explicitly stated high regime. -/
theorem monotone_action_growth_of_high (hh : HighActionGrowth) :
    MonotoneActionGrowth := by
  intro n f hf r hr hp
  by_cases hl : r ≤ lowCutoff
  · have hc := ck_low f hr.1.le hl
    have : gap f r ≤ 0 := sub_nonpos.mpr hc
    exact False.elim (not_lt_of_ge this hp)
  · have hrange : r ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hr.1], hr.2⟩
    have heq := Real.tanh_artanh hrange
    have hell : 31/20 ≤ Real.artanh r := by
      have hc : Real.tanh (31/20 : ℝ) < r := lt_of_not_ge hl
      have ha := Real.strictMonoOn_artanh
        (show Real.tanh (31/20 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 from
          ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩) hrange hc
      simpa only [Real.artanh_tanh] using ha.le
    have hgap : 0 < gap f (Real.tanh (Real.artanh r)) := by simpa only [heq] using hp
    by_cases hm : Real.artanh r ≤ 7/2
    · simpa only [heq] using middle_action_growth hf hell hm hgap
    · simpa only [heq] using hh n f hf (Real.artanh r) (le_of_not_ge hm) hgap

theorem main_of_high_action_growth (hh : HighActionGrowth) : MainTheorem :=
  main_of_monotone_action_growth (monotone_action_growth_of_high hh)

end MostInformativeBit
