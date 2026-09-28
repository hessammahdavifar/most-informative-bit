import MostInformativeBit.HighChannel

namespace MostInformativeBit.CutoffMargin
open Set Real ChannelProfiles ChannelBounds MiddleChannel HighChannel

lemma hasDerivAt_logF {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun v => Real.log (F v)) (-rate v) v := by
  have hh := (hasDerivAt_F hv).differentiableAt.hasDerivAt.log (ne_of_gt (F_pos hv))
  convert hh using 1
  unfold rate
  ring

lemma rate_eight_fifths {v : ℝ} (hv : 2 ≤ v) : 8/5 ≤ rate v := by
  have he0 : 0 < v := by linarith
  have hh := rate_lower he0
  have hb : (8:ℝ)/5 ≤ 4*v/(2*v+1) := by
    rw [le_div_iff₀ (by positivity : 0<2*v+1)]
    linarith
  exact hb.trans hh

lemma logF_rate_comparison {w ell : ℝ} (hw : 2 ≤ w) (hwe : w ≤ ell) :
    (8/5)*(ell-w) ≤ Real.log (F w)-Real.log (F ell) := by
  let f : ℝ → ℝ := fun v => Real.log (F v)+(8/5)*v
  have hd (v : ℝ) (hv : 0 < v) : HasDerivAt f (-rate v+8/5) v := by
    convert (hasDerivAt_logF hv).add ((hasDerivAt_id v).const_mul (8/5)) using 1 <;> try rfl
    ring
  have hm : AntitoneOn f (Ici w) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · intro v hv; exact (hd v (by linarith [show w≤v from hv])).continuousAt.continuousWithinAt
    · intro v hv
      rw [interior_Ici] at hv
      exact (hd v (by linarith [show w<v from hv])).differentiableAt.differentiableWithinAt
    · intro v hv
      rw [interior_Ici] at hv
      rw [(hd v (by linarith [show w<v from hv])).deriv]
      linarith [rate_eight_fifths (show 2≤v by linarith [show w<v from hv])]
  have hh := hm (show w∈Ici w from le_refl w) hwe hwe
  dsimp [f] at hh
  linarith

/-- The cutoff height lies within `5 exp(-ell)/3` of the channel height. -/
theorem cutoff_height {ell V : ℝ} (he : 7/2 ≤ ell) (hV : 0 < V)
    (hFV : F V = F ell/aCut ell) : 0 < ell-V ∧ ell-V < (5/3)*x ell := by
  have he0 : 0 < ell := by linarith
  have hx := x_pos ell
  have hx1 := x_lt he
  have ha := aCut_bounds ell
  have hFe := F_pos he0
  have hFV' : F V = F ell*(1+(8/3)*x ell) := by
    rw [hFV,aCut]
    field_simp
  have hflt : F ell < F V := by rw [hFV']; nlinarith
  have hVe : V < ell := by
    by_contra hh
    have hm := F_strictAnti.antitoneOn (show ell∈Ioi 0 from he0) (show V∈Ioi 0 from hV) (le_of_not_gt hh)
    linarith
  let w := ell-(5/3)*x ell
  have hw : 2 ≤ w := by dsimp [w]; linarith
  have hwe : w ≤ ell := by dsimp [w]; linarith
  have hcomp := logF_rate_comparison hw hwe
  have hden : 0 < 1+(8/3)*x ell := by positivity
  have hl := Real.log_lt_sub_one_of_pos hden (by nlinarith : 1+(8/3)*x ell ≠ 1)
  have hlog : Real.log (F V) < Real.log (F w) := by
    rw [hFV',Real.log_mul (ne_of_gt hFe) (ne_of_gt hden)]
    dsimp [w] at hcomp ⊢
    linarith
  have hFw : F V < F w := (Real.log_lt_log_iff (F_pos hV) (F_pos (by linarith : 0<w))).mp hlog
  have hwV : w < V := by
    by_contra hh
    have hm := F_strictAnti.antitoneOn (show V∈Ioi 0 from hV)
      (show w∈Ioi 0 from lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hw) (le_of_not_gt hh)
    linarith
  constructor
  · linarith
  · dsimp [w] at hwV
    linarith


lemma cutoff_brackets {ell : ℝ} (he : 7/2 ≤ ell) :
    1/4 < 8*(r ell)^2*(1-(r ell)^2/2)/(3+8*x ell)-
      (2*ell-5/3)*x ell/Real.log 2-5/(3*ell) ∧
    1/2 < 8/(3+8*x ell)*(1-(r ell)^2/(2*(gamma ell+2)))-10/(3*ell) := by
  have he0 : 0 < ell := by linarith
  have hr := r_bounds he
  have hr0 := r_pos he0
  have hr2 : (3:ℝ)/4 < (r ell)^2 := by nlinarith
  have hr21 : (r ell)^2 < 1 := by nlinarith
  have hx := x_pos ell
  have hx1 := x_lt he
  have hg : 7 < gamma ell := by linarith [gamma_gt_linear he]
  have hlog : (2:ℝ)/3 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hden : 0 < 3+8*x ell := by positivity
  have hprod : 15/32 < (r ell)^2*(1-(r ell)^2/2) := by
    nlinarith [mul_pos (show 0<(r ell)^2-3/4 by linarith) (show 0<5/4-(r ell)^2 by linarith)]
  have hfirst : 1 < 8*(r ell)^2*(1-(r ell)^2/2)/(3+8*x ell) := by
    rw [lt_div_iff₀ hden]
    nlinarith
  have hex : (2*ell-5/3)*x ell < (1:ℝ)/6 := by
    have hs := shift_x_bound he
    have hmul := mul_le_mul_of_nonneg_right (show 2*ell-5/3 ≤ (16:ℝ)/3*(1+(ell-7/2)) by linarith) hx.le
    nlinarith
  have hent : (2*ell-5/3)*x ell/Real.log 2 < (1:ℝ)/4 := by
    rw [div_lt_iff₀ (by linarith : 0<Real.log 2)]
    linarith
  have hlast : 5/(3*ell) < (1:ℝ)/2 := by
    rw [div_lt_iff₀ (by positivity : 0<3*ell)]
    linarith
  constructor
  · linarith
  · have hfrac : 2 < 8/(3+8*x ell) := by rw [lt_div_iff₀ hden]; linarith
    have hrad : (r ell)^2/(2*(gamma ell+2)) < (1:ℝ)/4 := by
      rw [div_lt_iff₀ (by positivity : 0<2*(gamma ell+2))]
      linarith
    have hlast' : 10/(3*ell) < (1:ℝ) := by
      rw [div_lt_iff₀ (by positivity : 0<3*ell)]
      linarith
    have hm := mul_lt_mul (a:=(2:ℝ)) hfrac
      (show (3:ℝ)/4 ≤ 1-(r ell)^2/(2*(gamma ell+2)) by linarith) (by norm_num)
      (by linarith : 0≤8/(3+8*x ell))
    nlinarith

noncomputable def parsevalMargin (ell v a : ℝ) : ℝ :=
  B ell/ell*v-r ell*c v-p ell*(d2 ell/2+db ell*a)

lemma parseval_margin_lower {ell V : ℝ} (he : 7/2 ≤ ell) (hV : 0 < V) (hVe : V ≤ ell) :
    -C ell*E ell/Real.log 2+p ell*db ell*(1-aCut ell)-B ell/ell*(ell-V) ≤
      parsevalMargin ell V (aCut ell) := by
  have he0 : 0 < ell := by linarith
  have hid := endpoint_margin_identity he
  have hc := c_strictMono.monotoneOn (show V∈Ioi 0 from hV) (show ell∈Ioi 0 from he0) hVe
  have hh := mul_le_mul_of_nonneg_left hc (r_pos he0).le
  unfold parsevalMargin db
  have hdiv : B ell/ell*ell = B ell := div_mul_cancel₀ _ (ne_of_gt he0)
  nlinarith

/-- Actual positive Parseval margin at the rational local cutoff. -/
theorem cutoff_margin {ell V : ℝ} (he : 7/2 ≤ ell) (hV : 0 < V)
    (hFV : F V = F ell/aCut ell) :
    x ell*(C ell/4+(lam ell)^2*(r ell)^2/2) < parsevalMargin ell V (aCut ell) := by
  have he0 : 0 < ell := by linarith
  have hheight := cutoff_height he hV hFV
  have hm := parseval_margin_lower he hV (by linarith [hheight.1])
  have hc := (C_bounds he).1
  have hE := E_upper he
  have hB := B_upper he
  have hx := x_pos ell
  have hr := r_pos he0
  have hla := lam_pos he0
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hBd : 0 < B ell/ell := (r_pos he0).trans (budget_slope he)
  have hEterm : -C ell*((x ell)^2*(2*ell-5/3))/Real.log 2 ≤ -C ell*E ell/Real.log 2 := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonpos_left hE (by linarith)) hlog.le
  have hBterm : B ell/ell*(ell-V) < (2*(lam ell)^2*(r ell)^2+C ell)/ell*((5/3)*x ell) := by
    have h1 := mul_lt_mul_of_pos_left hheight.2 hBd
    have h2 := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hB he0.le) (show 0≤(5/3)*x ell by positivity)
    exact h1.trans_le h2
  have hpdb := pdb_identity he
  have ha : 1-aCut ell = 8*x ell/(3+8*x ell) := by unfold aCut; field_simp <;> ring
  have hid :
      -C ell*((x ell)^2*(2*ell-5/3))/Real.log 2+p ell*db ell*(1-aCut ell)-
        (2*(lam ell)^2*(r ell)^2+C ell)/ell*((5/3)*x ell) =
      x ell*(C ell*(8*(r ell)^2*(1-(r ell)^2/2)/(3+8*x ell)-
        (2*ell-5/3)*x ell/Real.log 2-5/(3*ell))+
        (lam ell)^2*(r ell)^2*(8/(3+8*x ell)*(1-(r ell)^2/(2*(gamma ell+2)))-10/(3*ell))) := by
    rw [hpdb,ha]
    ring
  have hbr := cutoff_brackets he
  have h1 := mul_lt_mul_of_pos_left hbr.1 hc
  have h2 := mul_lt_mul_of_pos_left hbr.2 (mul_pos (pow_pos hla 2) (pow_pos hr 2))
  have h3 := mul_lt_mul_of_pos_left (show C ell/4+(lam ell)^2*(r ell)^2/2 <
      C ell*(8*(r ell)^2*(1-(r ell)^2/2)/(3+8*x ell)-
      (2*ell-5/3)*x ell/Real.log 2-5/(3*ell))+
      (lam ell)^2*(r ell)^2*(8/(3+8*x ell)*(1-(r ell)^2/(2*(gamma ell+2)))-10/(3*ell)) by linarith) hx
  rw [← hid] at h3
  linarith

end MostInformativeBit.CutoffMargin
