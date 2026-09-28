import MostInformativeBit.MiddleChannel
import MostInformativeBit.HighAngular
import MostInformativeBit.CoordinateDeficit
import MostInformativeBit.EntropyBounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Canonical high-channel inequalities from canonical-tail-checks.tex. -/
namespace MostInformativeBit.HighChannel
open Set Real ChannelProfiles ChannelBounds MiddleChannel

noncomputable def x (ell : ℝ) : ℝ := Real.exp (-ell)
noncomputable def d (ell : ℝ) : ℝ := ell/2+5/4
noncomputable def p (ell : ℝ) : ℝ := (lam ell+1/alpha ell)^2
noncomputable def b (ell : ℝ) : ℝ := (lam ell)^2*(2+1/gamma ell)
noncomputable def C (ell : ℝ) : ℝ := p ell*degWeight (gamma ell) (d ell)-b ell
noncomputable def B (ell : ℝ) : ℝ := 2*(theta ell)^2+C ell*phi (r ell)/Real.log 2
noncomputable def d1 (ell : ℝ) : ℝ := deficitCoeff (gamma ell) (d ell) (r ell) 1
noncomputable def d2 (ell : ℝ) : ℝ := deficitCoeff (gamma ell) (d ell) (r ell) 2
noncomputable def db (ell : ℝ) : ℝ := d1 ell-d2 ell/2
noncomputable def aCut (ell : ℝ) : ℝ := 1/(1+(8/3)*x ell)
noncomputable def E (ell : ℝ) : ℝ := h (r ell)-Real.log 2*(1-(r ell)^2)

lemma exp_seven_halves : (33:ℝ) < Real.exp (7/2) := by
  have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 7/2) 13
  norm_num [Finset.sum_range_succ, Nat.factorial] at hh
  linarith

lemma exp_tail {ell : ℝ} (he : 7/2 ≤ ell) : 33 < Real.exp ell :=
  exp_seven_halves.trans_le (Real.exp_le_exp.mpr he)

lemma x_pos (ell : ℝ) : 0 < x ell := Real.exp_pos _
lemma x_lt {ell : ℝ} (he : 7/2 ≤ ell) : x ell < 1/33 := by
  unfold x
  rw [Real.exp_neg]
  exact (inv_lt_comm₀ (Real.exp_pos ell) (by norm_num)).mpr (by simpa using exp_tail he)

lemma r_bounds {ell : ℝ} (he : 7/2 ≤ ell) : 99/100 < r ell ∧ r ell < 1 := by
  have hh := exp_tail he
  have hn : 0 < Real.exp ell^2+1 := by positivity
  constructor
  · rw [r_exp]
    apply (lt_sub_iff_add_lt).mpr
    have ht : 2/(Real.exp ell^2+1) < (1:ℝ)/100 := by
      rw [div_lt_div_iff₀ hn (by norm_num : (0:ℝ)<100)]
      nlinarith [sq_nonneg (Real.exp ell-33)]
    linarith
  · exact Real.tanh_lt_one _

lemma theta_tail {ell : ℝ} (he : 7/2 ≤ ell) : 3/2 < theta ell := by
  rw [theta_exp ell (by linarith)]
  have ha := arctan_le_self (x_pos ell).le
  have hx := x_lt he
  dsimp [x] at hx ha
  linarith [Real.pi_gt_d6]

lemma lam_gt_theta {ell : ℝ} (he : 0 < ell) : theta ell < lam ell := by
  unfold lam
  exact (lt_div_iff₀ (r_pos he)).mpr
    (mul_lt_of_lt_one_right (theta_pos he) (Real.tanh_lt_one ell))

lemma lam_lt_pi_half {ell : ℝ} (he : 0 < ell) : lam ell < Real.pi/2 := by
  have hr := r_pos he
  have hr1 : r ell < 1 := Real.tanh_lt_one ell
  have hs : 0 < Real.sqrt (1-(r ell)^2) := Real.sqrt_pos.mpr (by nlinarith)
  have hh := (arcsin_brackets ⟨hr.le,hr1.le⟩).2
  have ht : Real.pi*r ell/(2+Real.sqrt (1-(r ell)^2)) < Real.pi*r ell/2 :=
    div_lt_div_of_pos_left (mul_pos Real.pi_pos hr) (by norm_num) (by linarith)
  change theta ell ≤ _ at hh
  unfold lam
  apply (div_lt_iff₀ hr).mpr
  nlinarith [hh.trans_lt ht]

lemma lam_sq_lt {ell : ℝ} (he : 0 < ell) : (lam ell)^2 < 5/2 := by
  have hl := lam_lt_pi_half he
  have hp := lam_pos he
  have hpi := Real.pi_lt_d6
  have hpi0 := Real.pi_pos
  nlinarith

lemma gamma_lower {ell : ℝ} (he : 7/2 ≤ ell) :
    3*Real.exp ell/(4*ell) < gamma ell := by
  have he0 : 0 < ell := by linarith
  have ht := theta_tail he
  have hl := lam_gt_theta he0
  have hx := x_lt he
  have hi : 1/Real.exp ell = x ell := by simp [x,Real.exp_neg,one_div]
  have hs : Real.exp ell/2 < theta ell+Real.sinh ell := by
    rw [sinh_exp,hi]
    linarith
  have hp := mul_lt_mul (show (3:ℝ)/2 < lam ell by linarith) hs.le
    (by positivity : 0 < Real.exp ell/2) (lam_pos he0).le
  unfold gamma alpha
  rw [← mul_div_assoc]
  apply (div_lt_div_iff₀ (by positivity : 0<4*ell) he0).mpr
  nlinarith

lemma exp_shifted_cubic {ell : ℝ} (he : 7/2 ≤ ell) :
    33*(1+(ell-7/2)+(ell-7/2)^2/2+(ell-7/2)^3/6) < Real.exp ell := by
  have ht : 0 ≤ ell-7/2 := by linarith
  have hs := Real.sum_le_exp_of_nonneg ht 4
  norm_num [Finset.sum_range_succ,Nat.factorial] at hs
  have heq : Real.exp ell = Real.exp (7/2)*Real.exp (ell-7/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq]
  have hp : 0 < 1+(ell-7/2)+(ell-7/2)^2/2+(ell-7/2)^3/6 := by positivity
  exact mul_lt_mul exp_seven_halves hs hp (Real.exp_pos _).le

lemma gamma_gt_linear {ell : ℝ} (he : 7/2 ≤ ell) : ell+7/2 < gamma ell := by
  have hh := exp_shifted_cubic he
  have ht : 0 ≤ ell-7/2 := by linarith
  have hl := gamma_lower he
  have he0 : 0 < 4*ell := by linarith
  rw [div_lt_iff₀ he0] at hl
  have hp : 0 < 3*Real.exp ell-4*ell*(ell+7/2) := by
    nlinarith [sq_nonneg (ell-7/2),pow_nonneg ht 3]
  nlinarith

lemma gamma_pairing {ell : ℝ} (he : 7/2 ≤ ell) :
    4*(d ell-1)*(d ell-2) < gamma ell+d ell := by
  have hh := exp_shifted_cubic he
  have ht : 0 ≤ ell-7/2 := by linarith
  have hl := gamma_lower he
  have he0 : 0 < 4*ell := by linarith
  rw [div_lt_iff₀ he0] at hl
  have hp : 0 < 3*Real.exp ell-(4*ell^3-6*ell^2-8*ell) := by
    nlinarith [sq_nonneg (ell-7/2),pow_nonneg ht 3]
  unfold d
  nlinarith

lemma d_ge_three {ell : ℝ} (he : 7/2 ≤ ell) : 3 ≤ d ell := by unfold d; linarith

lemma multiplier_identity {ell t : ℝ} (he : 0 < ell) (ht : 0 ≤ t) :
    p ell*degWeight (gamma ell) t-b ell =
      (lam ell)^2*(t-2-(t-1)^2/(gamma ell+t)) := by
  have ha := ne_of_gt (alpha_pos he)
  have hl := ne_of_gt (lam_pos he)
  have hg := gamma_pos he
  have hgt : gamma ell+t ≠ 0 := by positivity
  have hgn := ne_of_gt hg
  unfold p degWeight b
  have hid : lam ell*alpha ell = gamma ell := rfl
  field_simp
  rw [← hid]
  ring

lemma C_identity {ell : ℝ} (he : 7/2 ≤ ell) :
    C ell = (lam ell)^2*(d ell-2-(d ell-1)^2/(gamma ell+d ell)) := by
  exact multiplier_identity (by linarith) (by linarith [d_ge_three he])

lemma C_bounds {ell : ℝ} (he : 7/2 ≤ ell) :
    0 < C ell ∧ C ell < (5/2)*(d ell-2) := by
  have he0 : 0 < ell := by linarith
  have hg := gamma_gt_linear he
  have hd := d_ge_three he
  have hgp := gamma_pos he0
  have hden : 0 < gamma ell+d ell := by linarith
  have hlp : 0 < (lam ell)^2 := pow_pos (lam_pos he0) 2
  have hq : 0 < (d ell-1)^2/(gamma ell+d ell) :=
    div_pos (sq_pos_of_pos (by linarith)) hden
  have hc : 0 < d ell-2-(d ell-1)^2/(gamma ell+d ell) := by
    apply sub_pos.mpr
    rw [div_lt_iff₀ hden]
    have hgd : 1 < gamma ell*(d ell-2) := by
      nlinarith
    nlinarith
  rw [C_identity he]
  constructor
  · exact mul_pos hlp hc
  · have hlt := mul_lt_mul_of_pos_left (show d ell-2-(d ell-1)^2/(gamma ell+d ell)<d ell-2 by linarith) hlp
    exact hlt.trans (mul_lt_mul_of_pos_right (lam_sq_lt he0) (by linarith))

lemma b_lt_six {ell : ℝ} (he : 7/2 ≤ ell) : b ell < 6 := by
  have he0 : 0 < ell := by linarith
  have hg : 7 < gamma ell := by linarith [gamma_gt_linear he]
  have hi : 1/gamma ell < (1:ℝ)/7 := one_div_lt_one_div_of_lt (by norm_num) hg
  have hl := lam_sq_lt he0
  have hp : 0 < (lam ell)^2 := pow_pos (lam_pos he0) 2
  unfold b
  have hh := mul_lt_mul_of_pos_left (show 2+1/gamma ell < (15:ℝ)/7 by linarith) hp
  nlinarith

/-- The two actual canonical spectral baseline signs on the entire high range. -/
theorem baseline_signs {ell : ℝ} (he : 7/2 ≤ ell) :
    0 < C ell ∧ 0 < gamma ell-b ell+C ell*(1/(2*Real.log 2)-1) := by
  have hc := C_bounds he
  have hb := b_lt_six he
  have hg := gamma_gt_linear he
  have hl0 : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl1 : Real.log 2 < 3/4 := by linarith [Real.log_two_lt_d9]
  have hf : (2:ℝ)/3 < 1/(2*Real.log 2) := by
    rw [lt_div_iff₀ (by positivity : 0<2*Real.log 2)]
    linarith
  have ht := mul_lt_mul_of_pos_left (show -(1:ℝ)/3 < 1/(2*Real.log 2)-1 by linarith) hc.1
  constructor
  · exact hc.1
  · dsimp [d] at hc
    nlinarith



lemma weight_difference {g t u : ℝ} (hg : 0 < g) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    degWeight g t-degWeight g u = (t-u)*g/(g+t)*g/(g+u) := by
  have hn : g+t ≠ 0 := by positivity
  have hm : g+u ≠ 0 := by positivity
  unfold degWeight
  field_simp <;> ring

lemma d1_identity {ell : ℝ} (he : 7/2 ≤ ell) :
    d1 ell = (d ell-1)*gamma ell/(gamma ell+d ell)*gamma ell/(gamma ell+1)*(r ell)^2 := by
  unfold d1 deficitCoeff
  norm_num only [Nat.cast_one, Nat.mul_one]
  rw [weight_difference (gamma_pos (by linarith)) (by linarith [d_ge_three he]) (by norm_num)]

lemma d2_identity {ell : ℝ} (he : 7/2 ≤ ell) :
    d2 ell = (d ell-2)*gamma ell/(gamma ell+d ell)*gamma ell/(gamma ell+2)*(r ell)^4 := by
  unfold d2 deficitCoeff
  norm_num only [Nat.cast_ofNat, Nat.reduceMul]
  rw [weight_difference (gamma_pos (by linarith)) (by linarith [d_ge_three he]) (by norm_num)]

lemma d_coeff_bounds {ell : ℝ} (he : 7/2 ≤ ell) :
    0 < d2 ell ∧ d2 ell < d1 ell ∧ 0 < db ell := by
  have he0 : 0 < ell := by linarith
  have hg := gamma_pos he0
  have hr := r_pos he0
  have hr1 := (r_bounds he).2
  have hd := d_ge_three he
  have hgd : 0 < gamma ell+d ell := by linarith
  have hq0 : 0 < (d ell-2)/(gamma ell+2) := div_pos (by linarith) (by positivity)
  have hq : (d ell-2)/(gamma ell+2) < (d ell-1)/(gamma ell+1) := by
    rw [div_lt_div_iff₀ (by positivity : 0<gamma ell+2) (by positivity : 0<gamma ell+1)]
    nlinarith
  have hr2 : (r ell)^2 < 1 := by nlinarith
  have hrq : (r ell)^4 < (r ell)^2 := by
    nlinarith [mul_pos (sq_pos_of_pos hr) (sub_pos.mpr hr2)]
  have hm := mul_lt_mul hq hrq.le (pow_pos hr 4) (le_of_lt (hq0.trans hq))
  have hgp : 0 < (gamma ell)^2/(gamma ell+d ell) := div_pos (pow_pos hg 2) hgd
  have hid1 : d1 ell = (gamma ell)^2/(gamma ell+d ell)*
      ((d ell-1)/(gamma ell+1)*(r ell)^2) := by rw [d1_identity he]; ring
  have hid2 : d2 ell = (gamma ell)^2/(gamma ell+d ell)*
      ((d ell-2)/(gamma ell+2)*(r ell)^4) := by rw [d2_identity he]; ring
  have hdp : 0 < d2 ell := by rw [hid2]; positivity
  have hlt : d2 ell < d1 ell := by
    rw [hid1,hid2]
    exact mul_lt_mul_of_pos_left hm hgp
  exact ⟨hdp,hlt,by unfold db; linarith⟩

lemma p_gt_two {ell : ℝ} (he : 7/2 ≤ ell) : 2 < p ell := by
  have he0 : 0 < ell := by linarith
  have ht := (theta_tail he).trans (lam_gt_theta he0)
  have ha := alpha_pos he0
  have hi : 0 < 1/alpha ell := by positivity
  unfold p
  nlinarith

/-- The strict coefficient bound required by the original-yield endpoint principle. -/
theorem endpoint_coefficient {ell : ℝ} (he : 7/2 ≤ ell) :
    3/16 < p ell*d2 ell/(2*r ell) := by
  have he0 : 0 < ell := by linarith
  have hr := r_pos he0
  have hrb := r_bounds he
  have hd := d_ge_three he
  have hg := gamma_gt_linear he
  have hgp := gamma_pos he0
  have hgd : 0 < gamma ell+d ell := by linarith
  have hq1 : 1/2 < gamma ell/(gamma ell+d ell) := by
    rw [lt_div_iff₀ hgd]
    dsimp [d]
    linarith
  have hq2 : 1/2 < gamma ell/(gamma ell+2) := by
    rw [lt_div_iff₀ (by positivity : 0<gamma ell+2)]
    linarith
  have hq := mul_lt_mul (a:=(1:ℝ)/2) hq1 hq2.le (by norm_num) (by linarith : 0≤gamma ell/(gamma ell+d ell))
  have hr3 : 3/4 < (r ell)^3 := by nlinarith [sq_nonneg (r ell-99/100),pow_pos hr 3]
  have hp : 1 < p ell/2 := by linarith [p_gt_two he]
  have hd1 : 1 ≤ d ell-2 := by linarith
  have hprod : 3/16 < (p ell/2)*(d ell-2)*
      (gamma ell/(gamma ell+d ell)* (gamma ell/(gamma ell+2)))*(r ell)^3 := by
    have hab : 1 < (p ell/2)*(d ell-2) := by nlinarith
    have hac : 1/4 < (p ell/2)*(d ell-2)*
        (gamma ell/(gamma ell+d ell)*(gamma ell/(gamma ell+2))) := by nlinarith
    nlinarith
  have hid : p ell*d2 ell/(2*r ell) = (p ell/2)*(d ell-2)*
      (gamma ell/(gamma ell+d ell)*(gamma ell/(gamma ell+2)))*(r ell)^3 := by
    rw [d2_identity he]
    field_simp <;> ring
  rwa [hid]

lemma log_trapezoid {t : ℝ} (ht : 0 ≤ t) :
    Real.log (1+t) ≤ t-t^2/(2*(1+t)) := by
  let f : ℝ → ℝ := fun t => t-t^2/(2*(1+t))-Real.log (1+t)
  have hd (t : ℝ) (ht : 0 ≤ t) : HasDerivAt f (t^2/(2*(1+t)^2)) t := by
    have hn : 1+t ≠ 0 := by positivity
    have hn2 : 2*(1+t) ≠ 0 := by positivity
    convert ((hasDerivAt_id t).sub (((hasDerivAt_id t).pow 2).div
      (((hasDerivAt_id t).const_add 1).const_mul 2) hn2)).sub
      (((hasDerivAt_id t).const_add 1).log hn) using 1 <;> try rfl
    dsimp
    field_simp <;> ring
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _)
    · intro t ht; exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact (hd t ht.le).hasDerivWithinAt
    · intro t ht; positivity
  have hh := hm (by simp : (0:ℝ) ∈ Ici 0) ht ht
  have hh0 : 0 ≤ t-t^2/(2*(1+t))-Real.log (1+t) := by simpa [f] using hh
  linarith



lemma q_eq_x_sq (ell : ℝ) : q ell = (x ell)^2 := by
  unfold q x
  rw [← Real.exp_nat_mul]
  congr 1
  norm_num <;> ring

lemma E_nonneg {ell : ℝ} (he : 0 < ell) : 0 ≤ E ell := by
  have hh := phi_quadratic_upper (show r ell ∈ Icc (-1) 1 from
    ⟨by linarith [r_pos he],(Real.tanh_lt_one ell).le⟩)
  unfold E phi at *
  linarith

/-- The entropy error bound used by all three high-height margins. -/
lemma E_upper {ell : ℝ} (he : 7/2 ≤ ell) : E ell ≤ (x ell)^2*(2*ell-5/3) := by
  have hq := q_pos ell
  have hn : 1+q ell ≠ 0 := by positivity
  have hlog := log_trapezoid hq.le
  have hL : (2:ℝ)/3 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hp : 0 < 4*Real.log 2+2*ell*(q ell)^2+2*ell*q ell-
      13*(q ell)^2/6-29*q ell/6-8/3 := by
    have h1 : 0 < 2*ell-13/6 := by linarith
    have h2 : 0 < 2*ell-29/6 := by linarith
    nlinarith [mul_pos h1 (sq_pos_of_pos hq),mul_pos h2 hq]
  have hid : (q ell)*(2*ell-5/3)-
      ((q ell)-(q ell)^2/(2*(1+q ell))+2*ell*q ell/(1+q ell)-
        Real.log 2*(1-((1-q ell)/(1+q ell))^2)) =
      (q ell)*(4*Real.log 2+2*ell*(q ell)^2+2*ell*q ell-
        13*(q ell)^2/6-29*q ell/6-8/3)/(1+q ell)^2 := by
    field_simp
    ring
  have hpos : 0 < (q ell)*(4*Real.log 2+2*ell*(q ell)^2+2*ell*q ell-
      13*(q ell)^2/6-29*q ell/6-8/3)/(1+q ell)^2 := by positivity
  rw [← hid] at hpos
  unfold E r
  rw [h_tanh_eq_q,tanh_eq_q,← q_eq_x_sq]
  linarith

lemma h_tail_upper {ell : ℝ} (he : 0 < ell) : h (r ell) < (2*ell+1)*(x ell)^2 := by
  have hq := q_pos ell
  have hn : 0 < 1+q ell := by positivity
  have hl := Real.log_lt_sub_one_of_pos hn (by linarith : 1+q ell ≠ 1)
  have hf : 2*ell*q ell/(1+q ell) < 2*ell*q ell := by
    exact div_lt_self (by positivity) (by linarith)
  unfold r
  rw [h_tanh_eq_q,← q_eq_x_sq]
  nlinarith

lemma ell_x_bound {ell : ℝ} (he : 7/2 ≤ ell) : ell*x ell < 7/66 := by
  have hh := exp_shifted_cubic he
  have ht : 0 ≤ ell-7/2 := by linarith
  have hlo : (66:ℝ)/7*ell < Real.exp ell := by
    nlinarith [sq_nonneg (ell-7/2),pow_nonneg ht 3]
  have he0 := Real.exp_pos ell
  unfold x
  rw [Real.exp_neg]
  change ell/Real.exp ell < 7/66
  rw [div_lt_iff₀ he0]
  linarith

noncomputable def K (v : ℝ) : ℝ := 2*v+(1+q v)*Real.log (1+q v)/q v
noncomputable def T (ell : ℝ) : ℝ := Real.exp ell*F ell/F (ell/2)

lemma K_bounds (v : ℝ) : 2*v+1 ≤ K v ∧ K v ≤ 2*v+1+q v/2 := by
  have hq := q_pos v
  have h1 : 0 < 1+q v := by positivity
  have h2 : 0 < q v+2 := by positivity
  have hl := Real.le_log_one_add_of_nonneg hq.le
  have ht : q v/(1+q v) ≤ 2*q v/(q v+2) := by
    rw [div_le_div_iff₀ h1 h2]
    nlinarith [sq_nonneg (q v)]
  have hh : q v ≤ (1+q v)*Real.log (1+q v) := by
    have hz := (div_le_iff₀ h1).mp (ht.trans hl)
    nlinarith only [hz]
  have hu := log_trapezoid hq.le
  have hu' := mul_le_mul_of_nonneg_left hu h1.le
  have hi : (1+q v)*(q v-(q v)^2/(2*(1+q v))) = q v+(q v)^2/2 := by field_simp <;> ring
  rw [hi] at hu'
  unfold K
  constructor
  · have : 1 ≤ (1+q v)*Real.log (1+q v)/q v := (le_div_iff₀ hq).mpr (by simpa using hh)
    linarith
  · have : (1+q v)*Real.log (1+q v)/q v ≤ 1+q v/2 :=
      (div_le_iff₀ hq).mpr (by nlinarith only [hu'])
    linarith

lemma F_K {v : ℝ} (hv : 0 < v) : F v = q v*K v/(1-q v) := by
  have hqpos := q_pos v
  have hq := ne_of_gt hqpos
  have hq1 : 1-q v ≠ 0 := by linarith [q_lt_one hv]
  have hqp : 1+q v ≠ 0 := by positivity
  unfold F K
  rw [h_tanh_eq_q,tanh_eq_q]
  field_simp <;> ring

lemma q_half (ell : ℝ) : q (ell/2) = x ell := by unfold q x; congr 1; ring

lemma T_identity {ell : ℝ} (he : 0 < ell) :
    T ell = K ell/((1+x ell)*K (ell/2)) := by
  have hx := x_pos ell
  have hx1 : x ell < 1 := by unfold x; rw [Real.exp_lt_one_iff]; linarith
  have hk : 0 < K (ell/2) := by linarith [(K_bounds (ell/2)).1]
  have heq : Real.exp ell*x ell = 1 := by unfold x; rw [← Real.exp_add]; simp
  have hn1 : 1-x ell ≠ 0 := by linarith
  have hn2 : 1-(x ell)^2 ≠ 0 := by nlinarith
  have hn3 : 1+x ell ≠ 0 := by positivity
  unfold T
  rw [F_K he,F_K (by linarith : 0<ell/2),q_half,q_eq_x_sq]
  rw [show Real.exp ell = 1/x ell from (eq_div_iff (ne_of_gt hx)).mpr heq]
  field_simp <;> ring

lemma T_bounds {ell : ℝ} (he : 7/2 ≤ ell) :
    (2*ell+1)/((ell+1+x ell/2)*(1+x ell)) ≤ T ell ∧
    T ell ≤ (2*ell+1+(x ell)^2/2)/((ell+1)*(1+x ell)) := by
  have he0 : 0 < ell := by linarith
  have hk := K_bounds ell
  have hkz := K_bounds (ell/2)
  rw [q_half] at hkz
  rw [q_eq_x_sq] at hk
  have hx := x_pos ell
  have hk0 : 0 < K ell := by linarith [hk.1]
  have hkz0 : 0 < K (ell/2) := by linarith [hkz.1]
  rw [T_identity he0]
  constructor
  · apply (div_le_div_iff₀ (by positivity : 0<(ell+1+x ell/2)*(1+x ell)) (by positivity)).mpr
    have hm : (2*ell+1)*K (ell/2) ≤ K ell*(ell+1+x ell/2) := by nlinarith [hk.1,hkz.2]
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) hx.le]
  · apply (div_le_div_iff₀ (by positivity) (by positivity : 0<(ell+1)*(1+x ell))).mpr
    have hm : K ell*(ell+1) ≤ (2*ell+1+(x ell)^2/2)*K (ell/2) := by nlinarith [hk.2,hkz.1]
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) hx.le]



lemma T_simple_bounds {ell : ℝ} (he : 7/2 ≤ ell) :
    5/3 < T ell ∧ T ell ≤ 2-1/(ell+1) := by
  have ht := T_bounds he
  have hx := x_pos ell
  have hx1 := x_lt he
  have hex := ell_x_bound he
  have he0 : 0 < ell := by linarith
  constructor
  · have hlow : 5/3 < (2*ell+1)/((ell+1+x ell/2)*(1+x ell)) := by
      rw [lt_div_iff₀ (by positivity : 0<(ell+1+x ell/2)*(1+x ell))]
      have hx2 : (x ell)^2 < (1:ℝ)/1089 := by nlinarith
      nlinarith
    exact hlow.trans_le ht.1
  · apply ht.2.trans
    have hden : 0 < (ell+1)*(1+x ell) := by positivity
    apply (div_le_iff₀ hden).mpr
    have hid : (2-1/(ell+1))*((ell+1)*(1+x ell)) = (2*ell+1)*(1+x ell) := by field_simp <;> ring
    rw [hid]
    nlinarith

noncomputable def k : ℝ := Real.exp (-(1:ℝ)/2)
lemma k_bounds : 3/5 < k ∧ k < 5/8 := by
  have hl := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤1/2) 6
  have hu := Real.exp_bound' (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1:ℝ)/2≤1) (by norm_num : 0<(8:ℕ))
  norm_num [Finset.sum_range_succ,Nat.factorial] at hl hu
  have hlo : (8:ℝ)/5 < Real.exp (1/2) := by linarith
  have hhi : Real.exp (1/2) < (5:ℝ)/3 := by linarith
  unfold k
  rw [show -(1:ℝ)/2 = -((1:ℝ)/2) by ring,Real.exp_neg]
  constructor
  · exact (lt_inv_comm₀ (by norm_num) (Real.exp_pos _)).mpr (by norm_num; linarith)
  · exact (inv_lt_comm₀ (Real.exp_pos _) (by norm_num)).mpr (by norm_num; linarith)

lemma kT_bounds {ell : ℝ} (he : 7/2 ≤ ell) :
    1 < k*T ell ∧ k*T ell < (5/8)*(2-1/(ell+1)) := by
  have ht := T_simple_bounds he
  have hk := k_bounds
  constructor
  · nlinarith
  · have hm := mul_lt_mul hk.2 ht.2 (by linarith : 0<T ell) (by norm_num : (0:ℝ)≤5/8)
    exact hm

lemma c_tail {ell : ℝ} (he : 7/2 ≤ ell) : 9/4 < c ell := by
  have ht := theta_tail he
  have hr := r_bounds he
  have he0 : 0 < ell := by linarith
  change 9/4 < (theta ell)^2/r ell
  rw [lt_div_iff₀ (r_pos he0)]
  nlinarith

lemma small_first_margin {ell : ℝ} (he : 7/2 ≤ ell) :
    1/3 < d ell-ell/c ell-k*T ell := by
  have hc := c_tail he
  have ht := (kT_bounds he).2
  have he0 : 0 < ell := by linarith
  have hi : ell/c ell < (4:ℝ)/9*ell := by
    rw [div_lt_iff₀ (by linarith : 0<c ell)]
    nlinarith
  have hb : (1:ℝ)/3 ≤ ell/18+5/(8*(ell+1)) := by
    have hp : 0 ≤ (2*ell-3)*(2*ell-7) := mul_nonneg (by linarith) (by linarith)
    have hn : 0 < 8*(ell+1) := by linarith
    have hid : ell/18+5/(8*(ell+1))-1/3 = (2*ell-3)*(2*ell-7)/(72*(ell+1)) := by field_simp <;> ring
    have : 0 ≤ (2*ell-3)*(2*ell-7)/(72*(ell+1)) := by positivity
    rw [← hid] at this
    linarith
  have hh : 5/(8*(ell+1)) = 5/8*(1/(ell+1)) := by field_simp <;> ring
  rw [hh] at hb
  unfold d
  linarith

lemma small_pairing_loss {ell : ℝ} (he : 7/2 ≤ ell) :
    (d ell-1)*(d ell-1-k*T ell)/(gamma ell+d ell) < 1/4 := by
  have ht := (kT_bounds he).1
  have hd := d_ge_three he
  have hg := gamma_pairing he
  have hgp := gamma_pos (show 0<ell by linarith)
  rw [div_lt_iff₀ (by linarith : 0<gamma ell+d ell)]
  have hp := mul_pos (show 0<d ell-1 by linarith) (show 0<k*T ell-1 by linarith)
  nlinarith

lemma shift_x_bound {ell : ℝ} (he : 7/2 ≤ ell) :
    (1+(ell-7/2))*x ell < 1/33 := by
  have hh := exp_shifted_cubic he
  have ht : 0 ≤ ell-7/2 := by linarith
  have hlo : 33*(1+(ell-7/2)) < Real.exp ell := by
    nlinarith [sq_nonneg (ell-7/2),pow_nonneg ht 3]
  unfold x
  rw [Real.exp_neg]
  change (1+(ell-7/2))/Real.exp ell < 1/33
  rw [div_lt_iff₀ (Real.exp_pos ell)]
  linarith

lemma small_decay_bound {ell : ℝ} (he : 7/2 ≤ ell) :
    2*(d ell-2)*(2*ell-5/3)*(x ell)^2 < 1/96 := by
  have ht : 0 ≤ ell-7/2 := by linarith
  have hx := x_pos ell
  have hb := shift_x_bound he
  have hb0 : 0 ≤ (1+(ell-7/2))*x ell := by positivity
  have hb2 : ((1+(ell-7/2))*x ell)^2 < (1:ℝ)/1089 := by nlinarith
  have hpoly : 2*(d ell-2)*(2*ell-5/3) ≤ (32:ℝ)/3*(1+(ell-7/2))^2 := by
    unfold d
    nlinarith [sq_nonneg (ell-7/2)]
  have hm := mul_le_mul_of_nonneg_right hpoly (sq_nonneg (x ell))
  nlinarith

lemma entropy_loss {ell : ℝ} (he : 7/2 ≤ ell) :
    (C ell/(lam ell)^2)*E ell/(Real.log 2*(r ell)^2) < 1/96 := by
  have he0 : 0 < ell := by linarith
  have hc := C_bounds he
  have helo := E_nonneg he0
  have hehi := E_upper he
  have hd := d_ge_three he
  have hl := lam_pos he0
  have hl2 := pow_pos hl 2
  have hr := r_bounds he
  have hx := x_pos ell
  have hlog : 2/3 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hr2 : (99:ℝ)^2/100^2 < (r ell)^2 := by nlinarith
  have hden : 1/2 < Real.log 2*(r ell)^2 := by nlinarith
  have hf : C ell/(lam ell)^2 < d ell-2 := by
    rw [C_identity he]
    have hn := ne_of_gt hl2
    field_simp
    have hgp := gamma_pos he0
    have hq : 0 < (d ell-1)^2/(gamma ell+d ell) := div_pos (sq_pos_of_pos (by linarith)) (by linarith)
    nlinarith
  have hf0 : 0 < C ell/(lam ell)^2 := div_pos hc.1 hl2
  have hm : (C ell/(lam ell)^2)*E ell ≤ (d ell-2)*((x ell)^2*(2*ell-5/3)) :=
    mul_le_mul hf.le hehi helo (by linarith)
  have hdec := small_decay_bound he
  rw [div_lt_iff₀ (by linarith : 0<Real.log 2*(r ell)^2)]
  nlinarith



lemma lam_mul_r {ell : ℝ} (he : 0 < ell) : lam ell*r ell = theta ell := by
  unfold lam
  exact div_mul_cancel₀ _ (ne_of_gt (r_pos he))

lemma p_identity {ell : ℝ} (he : 0 < ell) :
    p ell = (lam ell)^2*(gamma ell+1)^2/(gamma ell)^2 := by
  have ha := ne_of_gt (alpha_pos he)
  have hl := ne_of_gt (lam_pos he)
  unfold p gamma
  field_simp <;> ring

lemma B_identity (ell : ℝ) :
    B ell = 2*(theta ell)^2+C ell*(r ell)^2-C ell*E ell/Real.log 2 := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold B E phi
  field_simp <;> ring

noncomputable def smallMargin (ell : ℝ) : ℝ :=
  B ell/ell-r ell-p ell*lsiConst (gamma ell) (d ell)*(r ell)^2*F ell/((ell/2)*F (ell/2))

lemma small_pairing_identity {ell : ℝ} (he : 7/2 ≤ ell) :
    ell*smallMargin ell/(theta ell)^2 =
      d ell-ell/c ell-k*T ell-
      (d ell-1)*(d ell-1-k*T ell)/(gamma ell+d ell)-
      (C ell/(lam ell)^2)*E ell/(Real.log 2*(r ell)^2) := by
  have he0 : 0 < ell := by linarith
  have hgp := gamma_pos he0
  have hd := d_ge_three he
  have hgd : gamma ell+d ell ≠ 0 := by positivity
  have hgp1 : gamma ell+1 ≠ 0 := by positivity
  have hr := ne_of_gt (r_pos he0)
  have ht := ne_of_gt (theta_pos he0)
  have hf := ne_of_gt (F_pos (show 0<ell/2 by linarith))
  have hl := ne_of_gt (lam_pos he0)
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hexp : Real.exp (2*d ell-3) = Real.exp ell*k := by
    unfold d k
    rw [← Real.exp_add]
    congr 1
    ring
  unfold smallMargin lsiConst
  rw [B_identity,hexp,p_identity he0]
  change ell*((2*theta ell^2+C ell*r ell^2-C ell*E ell/Real.log 2)/ell-r ell-
    (lam ell^2*(gamma ell+1)^2/gamma ell^2)*
      (gamma ell^2*(Real.exp ell*k)/(2*(gamma ell+d ell)*(gamma ell+1)))*
      r ell^2*F ell/((ell/2)*F (ell/2)))/theta ell^2 = _
  rw [C_identity he]
  change _ = d ell-ell/(theta ell^2/r ell)-k*T ell-
    (d ell-1)*(d ell-1-k*T ell)/(gamma ell+d ell)-
    ((lam ell^2*(d ell-2-(d ell-1)^2/(gamma ell+d ell)))/lam ell^2)*E ell/(Real.log 2*r ell^2)
  unfold T
  rw [show theta ell = lam ell*r ell from (lam_mul_r he0).symm]
  field_simp <;> ring

/-- The small-height spectral margin is strictly positive, with the manuscript reserve. -/
theorem small_margin {ell : ℝ} (he : 7/2 ≤ ell) :
    7*(theta ell)^2/(96*ell) < smallMargin ell := by
  have hid := small_pairing_identity he
  have h1 := small_first_margin he
  have h2 := small_pairing_loss he
  have h3 := entropy_loss he
  have hp : 7/96 < ell*smallMargin ell/(theta ell)^2 := by linarith
  have he0 : 0 < ell := by linarith
  have ht2 : 0 < (theta ell)^2 := pow_pos (theta_pos he0) 2
  rw [lt_div_iff₀ ht2] at hp
  apply (div_lt_iff₀ (by positivity : 0<96*ell)).mpr
  nlinarith

/-- The actual high-channel budget slope strictly exceeds the channel radius. -/
theorem budget_slope {ell : ℝ} (he : 7/2 ≤ ell) : r ell < B ell/ell := by
  have he0 : 0 < ell := by linarith
  have hm := small_margin he
  have hs : 0 < smallMargin ell := by
    have ht2 : 0 < (theta ell)^2 := pow_pos (theta_pos he0) 2
    have hh : 0 < 7*(theta ell)^2/(96*ell) := by positivity
    linarith
  have hd := d_ge_three he
  have hg := gamma_pos he0
  have hr := r_pos he0
  have hf := F_pos he0
  have hfz := F_pos (show 0<ell/2 by linarith)
  have hp : 0 < p ell := by linarith [p_gt_two he]
  have hcost : 0 ≤ p ell*lsiConst (gamma ell) (d ell)*(r ell)^2*F ell/((ell/2)*F (ell/2)) := by
    unfold lsiConst
    positivity
  unfold smallMargin at hs
  linarith



lemma aCut_bounds (ell : ℝ) : 0 < aCut ell ∧ aCut ell < 1 := by
  have hx := x_pos ell
  unfold aCut
  constructor
  · positivity
  · exact (div_lt_one (by positivity)).mpr (by linarith)

lemma pd1_identity {ell : ℝ} (he : 7/2 ≤ ell) :
    p ell*d1 ell = (C ell+(lam ell)^2)*(r ell)^2 := by
  have h1 := multiplier_identity (ell:=ell) (t:=1) (by linarith) (by norm_num)
  norm_num at h1
  unfold d1 deficitCoeff C
  norm_num only [Nat.cast_one,Nat.mul_one]
  nlinarith only [congrArg (fun z : ℝ => z*(r ell)^2) h1]

lemma pd2_identity {ell : ℝ} (he : 7/2 ≤ ell) :
    p ell*d2 ell = (C ell+(lam ell)^2/(gamma ell+2))*(r ell)^4 := by
  have h2 := multiplier_identity (ell:=ell) (t:=2) (by linarith) (by norm_num)
  norm_num at h2
  unfold d2 deficitCoeff C
  norm_num only [Nat.cast_ofNat,Nat.reduceMul]
  simp only [div_eq_mul_inv]
  nlinarith only [congrArg (fun z : ℝ => z*(r ell)^4) h2]

lemma pdb_identity {ell : ℝ} (he : 7/2 ≤ ell) :
    p ell*db ell = C ell*((r ell)^2-(r ell)^4/2)+
      (lam ell)^2*((r ell)^2-(r ell)^4/(2*(gamma ell+2))) := by
  have h1 := pd1_identity he
  have h2 := pd2_identity he
  unfold db
  rw [mul_sub,← mul_div_assoc,h1,h2]
  have hg := gamma_pos (show 0<ell by linarith)
  field_simp <;> ring

lemma B_upper {ell : ℝ} (he : 7/2 ≤ ell) : B ell ≤ 2*(lam ell)^2*(r ell)^2+C ell := by
  have he0 : 0 < ell := by linarith
  have hc := (C_bounds he).1
  have helo := E_nonneg he0
  have hr := r_bounds he
  have hr0 := r_pos he0
  have hr2 : (r ell)^2 < 1 := by nlinarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : 0 ≤ C ell*E ell/Real.log 2 := by positivity
  rw [B_identity,show theta ell = lam ell*r ell from (lam_mul_r he0).symm]
  nlinarith [mul_pos hc (sub_pos.mpr hr2)]

lemma endpoint_margin_identity {ell : ℝ} (he : 7/2 ≤ ell) :
    B ell-p ell*d1 ell-r ell*c ell = -C ell*E ell/Real.log 2 := by
  have hr := ne_of_gt (r_pos (show 0<ell by linarith))
  rw [B_identity,pd1_identity he]
  change 2*(theta ell)^2+C ell*(r ell)^2-C ell*E ell/Real.log 2-
    (C ell+(lam ell)^2)*(r ell)^2-r ell*((theta ell)^2/r ell) = _
  rw [show theta ell = lam ell*r ell from (lam_mul_r (show 0<ell by linarith)).symm]
  field_simp <;> ring



lemma lam_sq_lt_P {ell : ℝ} (he : 0 < ell) : (lam ell)^2 < Real.pi^2/4 := by
  have hl := lam_lt_pi_half he
  have hp := lam_pos he
  nlinarith [Real.pi_pos]

lemma C_lt_lam_sq_mul {ell : ℝ} (he : 7/2 ≤ ell) : C ell < (lam ell)^2*(d ell-2) := by
  have he0 : 0<ell := by linarith
  have hg := gamma_pos he0
  have hd := d_ge_three he
  have hq : 0 < (d ell-1)^2/(gamma ell+d ell) :=
    div_pos (sq_pos_of_pos (by linarith)) (by linarith)
  rw [C_identity he]
  nlinarith [mul_pos (pow_pos (lam_pos he0) 2) hq]

lemma C_lt_P_mul {ell : ℝ} (he : 7/2 ≤ ell) : C ell < (Real.pi^2/4)*(d ell-2) := by
  exact (C_lt_lam_sq_mul he).trans
    (mul_lt_mul_of_pos_right (lam_sq_lt_P (by linarith)) (by linarith [d_ge_three he]))

lemma pdb_upper {ell : ℝ} (he : 7/2 ≤ ell) : p ell*db ell < (Real.pi^2/4)*d ell/2 := by
  have he0 : 0<ell := by linarith
  have hc := (C_bounds he).1
  have hCu := C_lt_P_mul he
  have hr := r_bounds he
  have hr0 := r_pos he0
  have hg := gamma_pos he0
  have hla := lam_pos he0
  have hls := lam_sq_lt_P he0
  have hq : 0 < (r ell)^4/(2*(gamma ell+2)) := by positivity
  have h1 : (r ell)^2-(r ell)^4/2 ≤ 1/2 := by nlinarith [sq_nonneg (1-(r ell)^2)]
  have h2 : (r ell)^2-(r ell)^4/(2*(gamma ell+2)) < 1 := by nlinarith
  have hm1 := mul_le_mul_of_nonneg_left h1 hc.le
  have hm2 := mul_lt_mul_of_pos_left h2 (pow_pos hla 2)
  rw [pdb_identity he]
  nlinarith

lemma half_height_a {ell : ℝ} (he : 7/2 ≤ ell) :
    F ell/F (ell/2) = x ell*T ell ∧ F ell/F (ell/2) < 2*x ell := by
  have hx := x_pos ell
  have heq : x ell*Real.exp ell = 1 := by unfold x; rw [← Real.exp_add]; simp
  have hid : F ell/F (ell/2) = x ell*T ell := by unfold T; rw [← mul_div_assoc,← mul_assoc,heq,one_mul]
  constructor
  · exact hid
  · rw [hid]
    have ht := (T_simple_bounds he).2
    have hp : 0<1/(ell+1) := by positivity
    nlinarith

lemma reciprocal_gamma {ell : ℝ} (he : 7/2 ≤ ell) :
    1/(2*(gamma ell+2)) < (2*ell/3)*x ell := by
  have hx := x_pos ell
  have hg := gamma_pos (show 0<ell by linarith)
  have hl := gamma_lower he
  have he0 : 0 < ell := by linarith
  rw [div_lt_iff₀ (by positivity : 0<4*ell)] at hl
  have heq : Real.exp ell*x ell = 1 := by unfold x; rw [← Real.exp_add]; simp
  have hm := mul_lt_mul_of_pos_right hl hx
  rw [mul_assoc 3,heq] at hm
  rw [div_lt_iff₀ (by positivity : 0<2*(gamma ell+2))]
  nlinarith

noncomputable def joinMargin (ell : ℝ) : ℝ :=
  B ell/2-r ell*c (ell/2)-p ell*(d2 ell/2+db ell*(F ell/F (ell/2)))

lemma join_identity {ell : ℝ} (he : 7/2 ≤ ell) :
    joinMargin ell = r ell*(c ell-c (ell/2))-
      (lam ell)^2*(r ell)^4/(2*(gamma ell+2))+
      (C ell/2)*(1-(r ell)^4-h (r ell)/Real.log 2)-p ell*db ell*(F ell/F (ell/2)) := by
  have hr := ne_of_gt (r_pos (show 0<ell by linarith))
  have hpd := pd2_identity he
  have hid : r ell*c ell = (theta ell)^2 := by unfold c r at *; field_simp
  unfold joinMargin B phi
  rw [mul_add,← mul_div_assoc,hpd]
  have hg := gamma_pos (show 0<ell by linarith)
  rw [show r ell*(c ell-c (ell/2)) = r ell*c ell-r ell*c (ell/2) by ring,hid]
  field_simp <;> ring

lemma join_penalty_bound {ell : ℝ} (he : 7/2 ≤ ell) :
    (lam ell)^2*(r ell)^4/(2*(gamma ell+2)) < (Real.pi^2/4)*(2*ell/3)*x ell := by
  have he0 : 0<ell := by linarith
  have hr := r_bounds he
  have hr0 := r_pos he0
  have hr2 : (r ell)^2 < 1 := by nlinarith
  have hr4 : (r ell)^4 < 1 := by nlinarith [sq_nonneg ((r ell)^2-1)]
  have hl := lam_pos he0
  have hlP := lam_sq_lt_P he0
  have hq := reciprocal_gamma he
  have hx := x_pos ell
  have hg := gamma_pos he0
  have hn : 0 < 1/(2*(gamma ell+2)) := by positivity
  have hp : (lam ell)^2*(r ell)^4 < Real.pi^2/4 := by
    nlinarith [mul_pos (pow_pos hl 2) (sub_pos.mpr hr4)]
  have hm := mul_lt_mul hp hq.le hn (show 0≤Real.pi^2/4 by positivity)
  convert hm using 1 <;> try rfl
  all_goals ring

lemma join_entropy_bound {ell : ℝ} (he : 7/2 ≤ ell) :
    (C ell/2)*(h (r ell)/Real.log 2) ≤
      (Real.pi^2/4)*(d ell-2)*(2*ell+1)*(x ell)^2/(2*Real.log 2) := by
  have he0 : 0<ell := by linarith
  have hc := (C_bounds he).1
  have hCu := C_lt_P_mul he
  have hhu := h_tail_upper he0
  have hh0 : 0<h (r ell) := by
    have hp := F_pos he0
    change 0<h (r ell)/r ell at hp
    exact (div_pos_iff.mp hp).resolve_right (by intro h; linarith [r_pos he0]) |>.1
  have hp0 : 0<(Real.pi^2/4)*(d ell-2) := by
    have hd : 0<d ell-2 := by linarith [d_ge_three he]
    have hpi := Real.pi_pos
    positivity
  have hm := mul_le_mul hCu.le hhu.le hh0.le hp0.le
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hh := div_le_div_of_nonneg_right hm (show 0≤2*Real.log 2 by positivity)
  convert hh using 1 <;> try rfl
  all_goals field_simp <;> ring

lemma join_deficit_bound {ell : ℝ} (he : 7/2 ≤ ell) :
    p ell*db ell*(F ell/F (ell/2)) < (Real.pi^2/4)*d ell*x ell := by
  have hp := pdb_upper he
  have ha := (half_height_a he).2
  have he0 : 0<ell := by linarith
  have hF := div_pos (F_pos he0) (F_pos (show 0<ell/2 by linarith))
  have hP : 0≤(Real.pi^2/4)*d ell/2 := by
    have hd := d_ge_three he
    positivity
  have hh := mul_lt_mul hp ha.le hF hP
  nlinarith only [hh]

/-- The actual positive spectral Parseval margin at half height. -/
theorem join_margin {ell : ℝ} (he : 7/2 ≤ ell) :
    (21/100)*(Real.pi^2/4)*Real.exp (-ell/2) < joinMargin ell := by
  have he0 : 0<ell := by linarith
  have hr := r_bounds he
  have hr0 := r_pos he0
  have hx := x_pos ell
  have hu := Real.exp_pos (-ell/2)
  have hp := Real.pi_pos
  have hc := (C_bounds he).1
  have hr2 : (r ell)^2 < 1 := by nlinarith
  have hr4 : (r ell)^4 < 1 := by nlinarith [sq_nonneg ((r ell)^2-1)]
  have hang := HighAngular.half_height_saving he
  have hang' := mul_lt_mul_of_pos_left hang hr0
  have hpen := join_penalty_bound he
  have hent := join_entropy_bound he
  have hdef := join_deficit_bound he
  have hres := HighAngular.joining_reserve he
  have hres' := mul_lt_mul_of_pos_left hres (show 0<(Real.pi^2/4)*Real.exp (-ell/2) by positivity)
  have hexp1 : Real.exp (-ell/2)*Real.exp (-ell/2) = x ell := by
    rw [← Real.exp_add]
    unfold x
    congr 1
    ring
  have hexp2 : Real.exp (-ell/2)*Real.exp (-3*ell/2) = (x ell)^2 := by
    rw [← Real.exp_add,← q_eq_x_sq]
    unfold q
    congr 1
    ring
  have hid : ((Real.pi^2/4)*Real.exp (-ell/2))*
      (5*r ell/3-(7*ell/6+5/4+8/Real.pi)*Real.exp (-ell/2)-
        ((ell/2-3/4)*(2*ell+1)/(2*Real.log 2))*Real.exp (-3*ell/2)) =
      r ell*(5*(Real.pi^2/4)/3)*Real.exp (-ell/2)-2*Real.pi*x ell-
      (Real.pi^2/4)*(2*ell/3)*x ell-(Real.pi^2/4)*d ell*x ell-
      (Real.pi^2/4)*(d ell-2)*(2*ell+1)*(x ell)^2/(2*Real.log 2) := by
    calc
      _ = r ell*(5*(Real.pi^2/4)/3)*Real.exp (-ell/2)-
          (Real.pi^2/4)*(7*ell/6+5/4+8/Real.pi)*(Real.exp (-ell/2)*Real.exp (-ell/2))-
          (Real.pi^2/4)*((ell/2-3/4)*(2*ell+1)/(2*Real.log 2))*
            (Real.exp (-ell/2)*Real.exp (-3*ell/2)) := by ring
      _ = _ := by rw [hexp1,hexp2]; unfold d; field_simp <;> ring
  rw [hid] at hres'
  change 5*(Real.pi^2/4)/3*Real.exp (-ell/2)-2*Real.pi*x ell < c ell-c (ell/2) at hang
  change r ell*(5*(Real.pi^2/4)/3*Real.exp (-ell/2)-2*Real.pi*x ell) < r ell*(c ell-c (ell/2)) at hang'
  rw [join_identity he]
  have hradloss := mul_pos (show 0<2*Real.pi*x ell by positivity) (show 0<1-r ell by linarith)
  have hdrop := mul_pos hc (sub_pos.mpr hr4)
  nlinarith only [hres',hang',hpen,hent,hdef,hradloss,hdrop]

end MostInformativeBit.HighChannel
