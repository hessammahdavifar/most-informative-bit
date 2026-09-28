import MostInformativeBit.ScalarEdge
import MostInformativeBit.LocalPropagation
import MostInformativeBit.PivotalGeometry

namespace MostInformativeBit
open ChannelProfiles

/-- The actual inverse-profile height of a coordinate in the high regime. -/
theorem coordinate_height_spec {ell a : ℝ} (he : 0 < ell)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    let v := ScalarEdge.Finv (h (Real.tanh ell)/(Real.tanh ell*a))
    0 < v ∧ v ≤ ell ∧ F ell/F v = a := by
  intro v
  have hr := CenteredSupport.tanh_pos he
  have hh := h_tanh_pos ell
  have hv := ScalarEdge.Finv_spec (div_pos hh (mul_pos hr ha))
  change 0 < v ∧ F v = h (Real.tanh ell)/(Real.tanh ell*a) at hv
  have hF : F v = F ell/a := by rw [hv.2]; simp only [F]; ring
  refine ⟨hv.1, ?_, ?_⟩
  · by_contra hn
    have hlt := F_strictAnti he hv.1 (lt_of_not_ge hn)
    have hle : F ell ≤ F ell/a := (le_div_iff₀ ha).mpr
      (mul_le_of_le_one_right (F_pos he).le ha1)
    rw [hF] at hlt
    linarith
  · rw [hF]
    field_simp [(F_pos he).ne']

/-- A positive gap excludes every singleton above any proved local cutoff. -/
theorem pivotalMean_lt_cutoff_of_gap {n : ℕ} (f : Cube n → Bool) (i : Fin n)
    {r a : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a)
    (hm : 0 ≤ localMargin r a) (hp : 0 < gap f r) : pivotalMean i f < a := by
  by_contra hn
  have hc := ck_of_local_cutoff i f hr0 hr1 ha
    ((le_of_not_gt hn).trans (le_abs_self _)) hm
  have hg : gap f r ≤ 0 := sub_nonpos.mpr hc
  linarith

end MostInformativeBit
