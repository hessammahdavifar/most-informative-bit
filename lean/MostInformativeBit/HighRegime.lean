import MostInformativeBit.HighGrowth
import MostInformativeBit.HighYield
import MostInformativeBit.HighLocal
import MostInformativeBit.HighCoordinate
import MostInformativeBit.RegimeSplit

namespace MostInformativeBit
open ChannelProfiles MiddleChannel HighChannel

/-- The full high-correlation growth proposition, with all scalar premises proved. -/
theorem high_action_growth {n : ℕ} {f : Cube n → Bool} (hf : Monotone f)
    {ell : ℝ} (he : 7/2 ≤ ell) (hp : 0 < gap f (Real.tanh ell)) :
    Real.tanh ell*ell < entropyAction (noise (Real.tanh ell) (signField f)) := by
  have he0 : 0 < ell := by linarith
  apply action_growth_of_coordinate_cost hf (D := d ell) (by linarith) (by linarith [d_ge_three he])
  · exact (baseline_signs he).1.le
  · exact (baseline_signs he).2.le
  · exact (budget_slope he).le
  · intro i hi
    let v := ScalarEdge.Finv (h (Real.tanh ell)/(Real.tanh ell*pivotalMean i f))
    have hv := coordinate_height_spec he0 hi (pivotalMean_le_one hf i)
    change 0 < v ∧ v ≤ ell ∧ F ell/F v = pivotalMean i f at hv
    have hF : F v = F ell/pivotalMean i f := by
      apply (eq_div_iff hi.ne').mpr
      have hh := (div_eq_iff (F_pos hv.1).ne').mp hv.2.2
      nlinarith only [hh]
    have hac : pivotalMean i f < HighChannel.aCut ell :=
      pivotalMean_lt_cutoff_of_gap f i (r_pos he0).le (Real.tanh_lt_one ell).le
        HighLocal.aCut_mem.1 (HighLocal.local_cutoff he).le hp
    exact HighYield.coordinate_cost he hi hac.le hv.1 hF
  · exact hp

theorem high_action_growth_holds : HighActionGrowth := by
  intro n f hf ell he hp
  exact high_action_growth hf he hp

end MostInformativeBit
