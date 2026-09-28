import Mathlib.Tactic

/-! Algebraic assembly of the two growth estimates in mechanism.tex.
All probabilistic and analytic inputs are explicit hypotheses.
-/
namespace MostInformativeBit

theorem growth_budget
    {r ell B k delta action W : ℝ}
    (hr : 0 < r) (hell : 0 < ell)
    (hB : r ≤ B/ell)
    (hW : W ≤ action/r)
    (hbudget : B + k*delta + (r-B/ell)*W ≤ action) :
    (k*ell/B)*delta ≤ action/r-ell := by
  have hBpos : 0 < B := by
    have hb := (le_div_iff₀ hell).mp hB
    exact lt_of_lt_of_le (mul_pos hr hell) hb
  have hcoef : r-B/ell ≤ 0 := sub_nonpos.mpr hB
  have hmul := mul_le_mul_of_nonpos_left hW hcoef
  have hcombined : B+k*delta+(r-B/ell)*(action/r) ≤ action := by
    linarith only [hmul, hbudget]
  have hscaled := mul_le_mul_of_nonneg_right hcombined (mul_pos hr hell).le
  have he : (B+k*delta+(r-B/ell)*(action/r))*(r*ell) =
      B*r*ell+k*delta*r*ell+r*action*ell-B*action := by
    field_simp
    <;> ring
  rw [he] at hscaled
  rw [le_sub_iff_add_le, le_div_iff₀ hr]
  have htarget : ((k*ell/B)*delta+ell)*r ≤ action := by
    apply (mul_le_mul_iff_right₀ hBpos).mp
    have hc : B*(((k*ell/B)*delta+ell)*r) =
        k*ell*delta*r+ell*r*B := by
      field_simp
    rw [hc]
    nlinarith only [hscaled]
  exact htarget

theorem middle_growth_closure
    {action r ell theta eta gamma delta variance retained meanCorrection meanSquare : ℝ}
    (hpositive : 0 < gamma) (hdelta : 0 < delta)
    (hvariance : retained ≤ variance)
    (henergy : 0 ≤ 2*theta^2-r*ell-eta/2)
    (hmean : 0 ≤ meanCorrection-(r*ell-theta^2)*meanSquare)
    (hbound : (2*theta^2-r*ell-eta/2)*(variance-retained) +
      meanCorrection-(r*ell-theta^2)*meanSquare+2*gamma*delta ≤ action-r*ell) :
    r*ell < action := by
  have hfirst := mul_nonneg henergy (sub_nonneg.mpr hvariance)
  have hstrict : 0 < 2*gamma*delta := by positivity
  linarith

theorem resolvent_multiplier_identity
    {lambda alpha s : ℝ} (ha : alpha ≠ 0) (hl : lambda ≠ 0)
    (hs : lambda*alpha+s ≠ 0) :
    lambda^2*(lambda*alpha-(lambda*alpha+1)^2/(lambda*alpha+s)) =
      (lambda+1/alpha)^2*(lambda*alpha*s/(lambda*alpha+s)) -
        lambda^2*(2+1/(lambda*alpha)) := by
  field_simp
  <;> ring

end MostInformativeBit
