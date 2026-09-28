import MostInformativeBit.HighChannel
import MostInformativeBit.CutoffMargin
import MostInformativeBit.ProfileMonotonicity
import MostInformativeBit.OriginalYield

/-! Assembly of the high-channel coordinate yield from the proved spectral margins. -/
namespace MostInformativeBit.HighYield
open Set Real ChannelProfiles MiddleChannel HighChannel

lemma a_eq_ratio {ell v a : ℝ} (hv : 0<v) (ha : 0<a) (hF : F v=F ell/a) :
    a=F ell/F v := by
  apply (eq_div_iff (ne_of_gt (F_pos hv))).mpr
  have hh := (eq_div_iff (ne_of_gt ha)).mp hF
  nlinarith only [hh]

/-- The LSI branch covers every positive height up to half the channel height. -/
theorem small_coordinate_cost {ell a v : ℝ} (he : 7/2≤ell) (ha : 0<a)
    (hv : 0<v) (hvz : v≤ell/2) (hF : F v=F ell/a) :
    p ell*deficitBound (gamma ell) (d ell) (r ell) a+r ell*a*c v ≤
      (B ell/ell)*(a*v) := by
  have he0 : 0<ell := by linarith
  have hr := r_pos he0
  have hg := gamma_pos he0
  have hd := d_ge_three he
  have hp : 0<p ell := by linarith [p_gt_two he]
  have hK : 0<lsiConst (gamma ell) (d ell) := by unfold lsiConst; positivity
  have hratio := ProfileMonotonicity.pivotal_ratio_le he0 hv hvz
  rw [← a_eq_ratio hv ha hF] at hratio
  have hc := c_le_self hv.le
  have hs := small_margin he
  have ht := theta_pos he0
  have hs0 : 0<smallMargin ell := by
    have hh : 0<7*(theta ell)^2/(96*ell) := by positivity
    linarith
  unfold smallMargin at hs0
  have hq : a ≤ F ell/((ell/2)*F (ell/2))*v := (div_le_iff₀ hv).mp hratio
  have h1 := mul_le_mul_of_nonneg_left hq (show 0≤p ell*lsiConst (gamma ell) (d ell)*(r ell)^2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left h1 ha.le
  have h3 := mul_le_mul_of_nonneg_left hc (show 0≤r ell*a by positivity)
  have h4 := mul_pos (mul_pos ha hv) hs0
  have hD : deficitBound (gamma ell) (d ell) (r ell) a ≤
      lsiConst (gamma ell) (d ell)*(r ell)^2*a^2 := min_le_left _ _
  have h5 := mul_le_mul_of_nonneg_left hD hp.le
  simp only [div_eq_mul_inv] at h2 h3 h4 h5 ⊢
  nlinarith only [h2,h3,h4,h5]

noncomputable def parsevalYield (ell v : ℝ) : ℝ :=
  (r ell*c v+p ell*d2 ell/2+p ell*db ell*F ell*(1/F v))/v

lemma parsevalYield_eq {ell v : ℝ} :
    parsevalYield ell v = (r ell*c v+p ell*(d2 ell/2+db ell*(F ell/F v)))/v := by
  unfold parsevalYield
  ring

lemma join_yield {ell : ℝ} (he : 7/2≤ell) : parsevalYield ell (ell/2) ≤ B ell/ell := by
  have he0 : 0<ell := by linarith
  have hj := join_margin he
  have hp : 0<(21/100)*(Real.pi^2/4)*Real.exp (-ell/2) := by positivity
  have hj0 : 0<joinMargin ell := by linarith
  unfold joinMargin at hj0
  rw [parsevalYield_eq]
  apply (div_le_iff₀ (by linarith : 0<ell/2)).mpr
  have hid : B ell/ell*(ell/2)=B ell/2 := by field_simp
  rw [hid]
  linarith

/-- The endpoint principle reduces all heights above half height to the cutoff margin.
The cutoff hypothesis is discharged by `CutoffMargin` in the final theorem below. -/
lemma coordinate_cost_reduction {ell V a v : ℝ} (he : 7/2≤ell) (hV : 0<V)
    (hFV : F V=F ell/aCut ell)
    (hcut : r ell*c V+p ell*(d2 ell/2+db ell*aCut ell) ≤ B ell/ell*V)
    (ha : 0<a) (hac : a≤aCut ell) (hv : 0<v) (hF : F v=F ell/a) :
    p ell*deficitBound (gamma ell) (d ell) (r ell) a+r ell*a*c v ≤
      (B ell/ell)*(a*v) := by
  by_cases hvz : v≤ell/2
  · exact small_coordinate_cost he ha hv hvz hF
  have he0 : 0<ell := by linarith
  have hp : 0<p ell := by linarith [p_gt_two he]
  have hac0 := (aCut_bounds ell).1
  have hfvV : F V≤F v := by
    rw [hFV,hF]
    exact div_le_div_of_nonneg_left (F_pos he0).le ha hac
  have hvV : v≤V := by
    by_contra hh
    have hm := F_strictAnti (show V∈Ioi 0 from hV) (show v∈Ioi 0 from hv) (lt_of_not_ge hh)
    linarith
  have hA : 5/32 ≤ (p ell*d2 ell/2)/r ell := by
    have hh := endpoint_coefficient he
    have hid : (p ell*d2 ell/2)/r ell = p ell*d2 ell/(2*r ell) := by ring
    rw [hid]
    linarith
  have hEP := OriginalYield.original_yield_no_interior_max
    (A0:=p ell*d2 ell/2) (A1:=p ell*db ell*F ell)
    (r_pos he0) hA (show 0<ell/2 by linarith) (show ell/2≤v by linarith) hvV
  change parsevalYield ell v ≤ max (parsevalYield ell (ell/2)) (parsevalYield ell V) at hEP
  have hVy : parsevalYield ell V ≤ B ell/ell := by
    rw [parsevalYield_eq,← a_eq_ratio hV hac0 hFV]
    exact (div_le_iff₀ hV).mpr hcut
  have hy : parsevalYield ell v ≤ B ell/ell :=
    hEP.trans (max_le (join_yield he) hVy)
  rw [parsevalYield_eq,← a_eq_ratio hv ha hF] at hy
  have hy' := (div_le_iff₀ hv).mp hy
  have hmul := mul_le_mul_of_nonneg_left hy' ha.le
  have hD : deficitBound (gamma ell) (d ell) (r ell) a ≤ d2 ell/2*a+db ell*a^2 := min_le_right _ _
  have hpD := mul_le_mul_of_nonneg_left hD hp.le
  nlinarith only [hmul,hpD]



/-- The actual coordinate-cost bound, with every channel inequality discharged. -/
theorem coordinate_cost {ell a v : ℝ} (he : 7/2≤ell) (ha : 0<a)
    (hac : a≤aCut ell) (hv : 0<v) (hF : F v=F ell/a) :
    p ell*deficitBound (gamma ell) (d ell) (r ell) a+r ell*a*c v ≤
      (B ell/ell)*(a*v) := by
  have he0 : 0<ell := by linarith
  have hac0 := (aCut_bounds ell).1
  obtain ⟨V,⟨hV,hFV⟩,_⟩ := ChannelBounds.existsUnique_height (div_pos (F_pos he0) hac0)
  apply coordinate_cost_reduction he hV hFV ?_ ha hac hv hF
  have hm := CutoffMargin.cutoff_margin he hV hFV
  have hc := (C_bounds he).1
  have hx := x_pos ell
  have hr := r_pos he0
  have hl := lam_pos he0
  have hp : 0<x ell*(C ell/4+(lam ell)^2*(r ell)^2/2) := by positivity
  unfold CutoffMargin.parsevalMargin at hm
  linarith

/-- The source's normalized high-channel yield test for all remaining coordinates. -/
theorem channel_yield {ell v : ℝ} (he : 7/2≤ell) (hv : 0<v)
    (hac : F ell/F v≤aCut ell) :
    r ell*c v/v+p ell*deficitBound (gamma ell) (d ell) (r ell) (F ell/F v)/
      ((F ell/F v)*v) ≤ B ell/ell := by
  have he0 : 0<ell := by linarith
  have hf := F_pos hv
  have hfe := F_pos he0
  have ha := div_pos hfe hf
  have hF : F v=F ell/(F ell/F v) := by field_simp
  have hh := coordinate_cost he ha hac hv hF
  have hid : r ell*c v/v+p ell*deficitBound (gamma ell) (d ell) (r ell) (F ell/F v)/
      ((F ell/F v)*v) =
      (p ell*deficitBound (gamma ell) (d ell) (r ell) (F ell/F v)+r ell*(F ell/F v)*c v)/
      ((F ell/F v)*v) := by field_simp <;> ring
  rw [hid]
  exact (div_le_iff₀ (mul_pos ha hv)).mpr hh

/-- Complete scalar hypotheses required by the canonical high-growth mechanism. -/
theorem high_channel_checks {ell : ℝ} (he : 7/2≤ell) :
    0≤C ell ∧ 0≤gamma ell-b ell+C ell*(1/(2*Real.log 2)-1) ∧
    r ell≤B ell/ell ∧
    ∀ a v, 0<a → a≤aCut ell → 0<v → F v=F ell/a →
      p ell*deficitBound (gamma ell) (d ell) (r ell) a+r ell*a*c v ≤
        (B ell/ell)*(a*v) :=
  ⟨(baseline_signs he).1.le,(baseline_signs he).2.le,(budget_slope he).le,
    fun _ _ ha hac hv hF => coordinate_cost he ha hac hv hF⟩

end MostInformativeBit.HighYield
