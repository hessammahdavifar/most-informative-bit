import MostInformativeBit.ChannelBounds
import MostInformativeBit.IntervalBounds

/-! Analytic middle-channel reserves: monotonicity, fixed endpoints, and curvature. -/
namespace MostInformativeBit.MiddleChannel
open Set Real ChannelProfiles ChannelBounds IntervalBounds

namespace ProfileBounds

lemma s_strictAnti : StrictAntiOn s (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi _)
  · intro v hv; exact (hasDerivAt_s hv).continuousAt.continuousWithinAt
  · intro v hv
    rw [interior_Ioi] at hv
    rw [(hasDerivAt_s hv).deriv]
    exact sd_neg hv

lemma s_antitone : AntitoneOn s (Ioi 0) := s_strictAnti.antitoneOn

lemma hasDerivAt_theta_div_tanh {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun v => theta v/Real.tanh v)
      ((Real.sinh v-theta v)/(Real.sinh v)^2) v := by
  convert (hasDerivAt_theta v).div (hasDerivAt_tanh v) (CenteredSupport.tanh_pos hv).ne' using 1 <;> try rfl
  rw [Real.tanh_eq_sinh_div_cosh]
  have hs := (Real.sinh_pos_iff.mpr hv).ne'
  have hc := (Real.cosh_pos v).ne'
  field_simp

lemma theta_div_tanh_strictMono : StrictMonoOn (fun v => theta v/Real.tanh v) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi _)
  · intro v hv; exact (hasDerivAt_theta_div_tanh hv).continuousAt.continuousWithinAt
  · intro v hv
    rw [interior_Ioi] at hv
    rw [(hasDerivAt_theta_div_tanh hv).deriv]
    exact div_pos (sub_pos.mpr ((theta_lt_self hv).trans (self_lt_sinh hv)))
      (sq_pos_of_pos (Real.sinh_pos_iff.mpr hv))

lemma theta_div_tanh_monotone : MonotoneOn (fun v => theta v/Real.tanh v) (Ioi 0) :=
  theta_div_tanh_strictMono.monotoneOn

noncomputable def angleSinh (v : ℝ) : ℝ := theta v+Real.sinh v
noncomputable def angleSinhSlope (v : ℝ) : ℝ := 1/Real.cosh v+Real.cosh v
noncomputable def angleSinhDefect (v : ℝ) : ℝ := v*angleSinhSlope v-angleSinh v

lemma hasDerivAt_angleSinh (v : ℝ) : HasDerivAt angleSinh (angleSinhSlope v) v :=
  (hasDerivAt_theta v).add (Real.hasDerivAt_sinh v)

lemma hasDerivAt_angleSinhSlope (v : ℝ) :
    HasDerivAt angleSinhSlope (Real.sinh v*(1-1/(Real.cosh v)^2)) v := by
  have hh := ((hasDerivAt_const v (1:ℝ)).div (Real.hasDerivAt_cosh v) (Real.cosh_pos v).ne').add
    (Real.hasDerivAt_cosh v)
  refine hh.congr_deriv ?_
  ring

lemma hasDerivAt_angleSinhDefect (v : ℝ) :
    HasDerivAt angleSinhDefect (v*Real.sinh v*(1-1/(Real.cosh v)^2)) v := by
  convert ((hasDerivAt_id' v).mul (hasDerivAt_angleSinhSlope v)).sub
    (hasDerivAt_angleSinh v) using 1 <;> try rfl
  dsimp [angleSinhSlope]
  ring

lemma angleSinhDefect_pos {v : ℝ} (hv : 0 < v) : 0 < angleSinhDefect v := by
  have hm : StrictMonoOn angleSinhDefect (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · intro v _; exact (hasDerivAt_angleSinhDefect v).continuousAt.continuousWithinAt
    · intro v hv
      rw [interior_Ici] at hv
      rw [(hasDerivAt_angleSinhDefect v).deriv]
      have hc := Real.one_lt_cosh.mpr (ne_of_gt hv)
      have hq : 1/(Real.cosh v)^2 < 1 := (div_lt_one (sq_pos_of_pos (Real.cosh_pos v))).mpr (by nlinarith)
      exact mul_pos (mul_pos hv (Real.sinh_pos_iff.mpr hv)) (sub_pos.mpr hq)
  have hh := hm (by simp : (0:ℝ) ∈ Ici 0) hv.le hv
  simpa [angleSinhDefect,angleSinh,theta] using hh

lemma theta_add_sinh_div_strictMono :
    StrictMonoOn (fun v => (theta v+Real.sinh v)/v) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi _)
  · intro v hv
    exact ((hasDerivAt_angleSinh v).div (hasDerivAt_id v) (ne_of_gt hv)).continuousAt.continuousWithinAt
  · intro v hv
    rw [interior_Ioi] at hv
    change 0 < deriv (angleSinh / id) v
    rw [((hasDerivAt_angleSinh v).div (hasDerivAt_id v) (ne_of_gt hv)).deriv]
    have hh := angleSinhDefect_pos hv
    apply div_pos _ (sq_pos_of_pos hv)
    simpa only [angleSinhDefect,id_eq,mul_one,one_mul,mul_comm] using hh

lemma theta_add_sinh_div_monotone :
    MonotoneOn (fun v => (theta v+Real.sinh v)/v) (Ioi 0) :=
  theta_add_sinh_div_strictMono.monotoneOn

lemma two_lt_theta_add_sinh_div {v : ℝ} (hv : 0 < v) :
    2 < (theta v+Real.sinh v)/v := by
  have hd (v : ℝ) : HasDerivAt (fun v => angleSinh v-2*v) (angleSinhSlope v-2) v := by
    convert (hasDerivAt_angleSinh v).sub ((hasDerivAt_id v).const_mul 2) using 1 <;> try rfl
    ring
  have hm : StrictMonoOn (fun v => angleSinh v-2*v) (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · intro v _; exact (hd v).continuousAt.continuousWithinAt
    · intro v hv
      rw [interior_Ici] at hv
      rw [(hd v).deriv]
      have hc := Real.cosh_pos v
      have hc1 := Real.one_lt_cosh.mpr (ne_of_gt hv)
      have he : angleSinhSlope v-2 = (Real.cosh v-1)^2/Real.cosh v := by
        unfold angleSinhSlope
        field_simp
        ring
      rw [he]
      exact div_pos (sq_pos_of_pos (sub_pos.mpr hc1)) hc
  have hh := hm (by simp : (0:ℝ) ∈ Ici 0) hv.le hv
  simp only [angleSinh,theta,Real.tanh_zero,Real.arcsin_zero,Real.sinh_zero,add_zero,mul_zero,sub_self] at hh
  apply (lt_div_iff₀ hv).mpr
  change 0 < theta v+Real.sinh v-2*v at hh
  linarith

end ProfileBounds

noncomputable def r (ell : ℝ) : ℝ := Real.tanh ell
noncomputable def lam (ell : ℝ) : ℝ := theta ell/r ell
noncomputable def alpha (ell : ℝ) : ℝ := (theta ell+Real.sinh ell)/ell
noncomputable def gamma (ell : ℝ) : ℝ := lam ell*alpha ell
noncomputable def eta (ell : ℝ) : ℝ := (theta ell)^2*(gamma ell/(gamma ell+1))
noncomputable def beta (ell : ℝ) : ℝ := 2*r ell/eta ell
noncomputable def H (v : ℝ) : ℝ := v-c v
noncomputable def energyReserve (ell : ℝ) : ℝ := 2*(theta ell)^2-r ell*ell-eta ell/2
noncomputable def meanReserve (ell : ℝ) : ℝ :=
  gamma ell-2*(theta ell)^2/(Real.sinh ell)^2-lam ell/alpha ell-r ell*ell

lemma r_pos {ell : ℝ} (he : 0 < ell) : 0 < r ell := CenteredSupport.tanh_pos he
lemma alpha_pos {ell : ℝ} (he : 0 < ell) : 0 < alpha ell := by
  unfold alpha
  exact div_pos (add_pos (theta_pos he) (Real.sinh_pos_iff.mpr he)) he
lemma lam_pos {ell : ℝ} (he : 0 < ell) : 0 < lam ell := div_pos (theta_pos he) (r_pos he)
lemma gamma_pos {ell : ℝ} (he : 0 < ell) : 0 < gamma ell := mul_pos (lam_pos he) (alpha_pos he)
lemma eta_pos {ell : ℝ} (he : 0 < ell) : 0 < eta ell := by
  have hg := gamma_pos he
  have ht := theta_pos he
  unfold eta
  positivity
lemma beta_pos {ell : ℝ} (he : 0 < ell) : 0 < beta ell := by
  unfold beta
  exact div_pos (mul_pos (by norm_num) (r_pos he)) (eta_pos he)

lemma arctan_lower_cubic {z : ℝ} (hz : 0 ≤ z) : z-z^3/3 ≤ Real.arctan z := by
  have hd (z : ℝ) : HasDerivAt (fun z => Real.arctan z-z+z^3/3)
      (z^4/(1+z^2)) z := by
    convert ((Real.hasDerivAt_arctan z).sub (hasDerivAt_id z)).add
      (((hasDerivAt_id z).pow 3).div_const 3) using 1 <;> try rfl
    dsimp
    field_simp
    ring
  have hh := nonneg_of_deriv_nonneg hd (by simp) (fun z _ => by positivity) hz
  linarith

lemma arctan_le_self {z : ℝ} (hz : 0 ≤ z) : Real.arctan z ≤ z := by
  have hh := CenteredSupport.arctan_le_rational hz
  have hp : 0 < 15+9*z^2 := by positivity
  have hr : z*(15+4*z^2)/(15+9*z^2) ≤ z := by
    apply (div_le_iff₀ hp).mpr
    nlinarith [pow_nonneg hz 3]
  exact hh.trans hr

lemma theta_exp (v : ℝ) (hv : 0 ≤ v) :
    theta v = Real.pi/2-2*Real.arctan (Real.exp (-v)) := by
  have he : 0 < Real.exp (-v) := Real.exp_pos _
  have he1 : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have ha : 0 ≤ Real.arctan (Real.exp (-v)) := Real.arctan_nonneg.mpr he.le
  have hb : Real.arctan (Real.exp (-v)) ≤ Real.pi/4 := by
    rw [← Real.arctan_one]
    exact Real.arctan_le_arctan_iff.mpr he1
  have heq : Real.exp (-v)^2 = q v := by
    unfold q
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  unfold theta
  symm
  apply Eq.symm
  apply Real.arcsin_eq_of_sin_eq
  · rw [Real.sin_sub, Real.sin_pi_div_two, Real.cos_pi_div_two]
    simp only [one_mul, zero_mul, sub_zero]
    rw [Real.cos_two_mul, Real.cos_sq_arctan, heq, tanh_eq_q]
    have hq := q_pos v
    field_simp
    ring
  · constructor <;> linarith [Real.pi_pos]

lemma theta_enclosure_of_pi {v lo hi piLo piHi : ℝ} (hv : 0 ≤ v) (hl : 0 < lo)
    (he : Encloses (Real.exp v) lo hi) (hpi : Encloses Real.pi piLo piHi) :
    Encloses (theta v) (piLo/2-2/lo)
      (piHi/2-2/hi+2/(3*lo^3)) := by
  have hhi : 0 < hi := lt_of_lt_of_le hl (he.1.trans he.2)
  have hz := inv_pos he hl
  have hpos : 0 ≤ Real.exp (-v) := (Real.exp_pos _).le
  have ha := arctan_le_self hpos
  have hb := arctan_lower_cubic hpos
  rw [Real.exp_neg] at ha hb
  have hzlo : 1/hi ≤ (Real.exp v)⁻¹ := by simpa only [one_div] using hz.1
  have hzhi : (Real.exp v)⁻¹ ≤ 1/lo := by simpa only [one_div] using hz.2
  have hc := pow_le_pow_left₀ (inv_nonneg.mpr (Real.exp_pos v).le) hzhi 3
  rw [theta_exp v hv, Real.exp_neg]
  constructor
  · ring_nf at ha hzhi ⊢
    linarith [hpi.1]
  · have hh : (1/lo)^3 = 1/lo^3 := by ring
    rw [hh] at hc
    ring_nf at hb hzlo hc ⊢
    linarith [hpi.2]

lemma theta_enclosure {v lo hi : ℝ} (hv : 0 ≤ v) (hl : 0 < lo)
    (he : Encloses (Real.exp v) lo hi) :
    Encloses (theta v) (3.141592/2-2/lo)
      (3.141593/2-2/hi+2/(3*lo^3)) :=
  theta_enclosure_of_pi hv hl he ⟨Real.pi_gt_d6.le,Real.pi_lt_d6.le⟩

lemma r_exp (v : ℝ) : r v = 1-2/(Real.exp v ^ 2+1) := by
  unfold r
  rw [CenteredSupport.tanh_exp_two, show 2*v=v+v by ring, Real.exp_add]
  field_simp
  ring

lemma sinh_exp (v : ℝ) : Real.sinh v = (Real.exp v-1/Real.exp v)/2 := by
  rw [Real.sinh_eq, Real.exp_neg, one_div]

lemma unit_fraction_enclosure {x lo hi : ℝ} (hx : Encloses x lo hi) (hl : 0 ≤ lo) :
    Encloses (x/(x+1)) (lo/(lo+1)) (hi/(hi+1)) := by
  have hx0 : 0 ≤ x := hl.trans hx.1
  have hhi : 0 ≤ hi := hx0.trans hx.2
  constructor
  · rw [div_le_div_iff₀ (by positivity : 0 < lo+1) (by positivity : 0 < x+1)]
    nlinarith [hx.1]
  · rw [div_le_div_iff₀ (by positivity : 0 < x+1) (by positivity : 0 < hi+1)]
    nlinarith [hx.2]




/-- Twice integrating a lower bound on the second derivative gives a quadratic support. -/
lemma quadratic_lower_of_second_derivative {f f' f'' : ℝ → ℝ} {a κ x : ℝ}
    (hf : ∀ t, a ≤ t → HasDerivAt f (f' t) t)
    (hf' : ∀ t, a ≤ t → HasDerivAt f' (f'' t) t)
    (hκ : ∀ t, a ≤ t → κ ≤ f'' t) (hx : a ≤ x) :
    f a+f' a*(x-a)+κ/2*(x-a)^2 ≤ f x := by
  have hd (t : ℝ) (ht : a ≤ t) :
      HasDerivAt (fun t => f' t-κ*(t-a)) (f'' t-κ) t := by
    convert (hf' t ht).sub (((hasDerivAt_id t).sub_const a).const_mul κ) using 1 <;> try rfl
    ring
  have hm : MonotoneOn (fun t => f' t-κ*(t-a)) (Ici a) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _)
    · intro t ht; exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht; exact (hd t (interior_subset ht)).hasDerivWithinAt
    · intro t ht; exact sub_nonneg.mpr (hκ t (interior_subset ht))
  have hfirst (t : ℝ) (ht : a ≤ t) : f' a+κ*(t-a) ≤ f' t := by
    have hh := hm (by simp : a ∈ Ici a) ht ht
    dsimp at hh
    linarith
  have he (t : ℝ) (ht : a ≤ t) :
      HasDerivAt (fun t => f t-f a-f' a*(t-a)-κ/2*(t-a)^2)
        (f' t-f' a-κ*(t-a)) t := by
    convert ((hf t ht).sub_const (f a) |>.sub
      (((hasDerivAt_id t).sub_const a).const_mul (f' a))).sub
      ((((hasDerivAt_id t).sub_const a).pow 2).const_mul (κ/2)) using 1 <;> try rfl
    dsimp
    ring
  have hmono : MonotoneOn (fun t => f t-f a-f' a*(t-a)-κ/2*(t-a)^2) (Ici a) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _)
    · intro t ht; exact (he t ht).continuousAt.continuousWithinAt
    · intro t ht; exact (he t (interior_subset ht)).hasDerivWithinAt
    · intro t ht; have hh := hfirst t (interior_subset ht); linarith
  have hh := hmono (by simp : a ∈ Ici a) hx hx
  dsimp at hh
  nlinarith

noncomputable def Y (v : ℝ) : ℝ := c v+theta v*Real.cosh v-r v*v^2-6*v/5
noncomputable def Yd (v : ℝ) : ℝ :=
  cd v+1+theta v*Real.sinh v-v^2/(Real.cosh v)^2-2*r v*v-6/5
noncomputable def T (v : ℝ) : ℝ := theta v*Real.cosh v-r v
noncomputable def Ydd (v : ℝ) : ℝ :=
  T v*(1-2*(1-s v)/(Real.sinh v)^2)+2*v/(Real.cosh v)^2*(r v*v-2)
noncomputable def Z (v : ℝ) : ℝ := (Real.pi+1)*r v+2*Real.sinh v-(5*Real.pi/3)*v
noncomputable def Zd (v : ℝ) : ℝ := (Real.pi+1)/(Real.cosh v)^2+2*Real.cosh v-5*Real.pi/3
noncomputable def Zdd (v : ℝ) : ℝ := 2*Real.sinh v-2*(Real.pi+1)*r v/(Real.cosh v)^2
noncomputable def sechWeight (v : ℝ) : ℝ := v/(Real.cosh v)^2

lemma hasDerivAt_r (v : ℝ) : HasDerivAt r (1/(Real.cosh v)^2) v := hasDerivAt_tanh v

lemma sd_eq_T {v : ℝ} (hv : 0<v) : sd v = -T v/(Real.sinh v)^2 := by
  have hc := ne_of_gt (Real.cosh_pos v)
  have hs := ne_of_gt (Real.sinh_pos_iff.mpr hv)
  unfold sd T s r
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  try ring

lemma hasDerivAt_Y {v : ℝ} (hv : 0<v) : HasDerivAt Y (Yd v) v := by
  have hc := ne_of_gt (Real.cosh_pos v)
  convert (((hasDerivAt_c hv).add ((hasDerivAt_theta v).mul (Real.hasDerivAt_cosh v))).sub
    ((hasDerivAt_r v).mul ((hasDerivAt_id v).pow 2))).sub
    (((hasDerivAt_id v).const_mul 6).div_const 5) using 1 <;> try rfl
  dsimp [Yd]
  field_simp
  try ring

lemma hasDerivAt_Yd {v : ℝ} (hv : 0<v) : HasDerivAt Yd (Ydd v) v := by
  have hc := ne_of_gt (Real.cosh_pos v)
  have hs := ne_of_gt (Real.sinh_pos_iff.mpr hv)
  have hc' := (hasDerivAt_cd hv)
  rw [sd_eq_T hv] at hc'
  convert (((((hc'.add_const 1).add ((hasDerivAt_theta v).mul (Real.hasDerivAt_sinh v))).sub
    (((hasDerivAt_id v).pow 2).div ((Real.hasDerivAt_cosh v).pow 2) (pow_ne_zero 2 hc))).sub
    ((((hasDerivAt_r v).const_mul 2).mul (hasDerivAt_id v)))).sub_const (6/5)) using 1 <;> try rfl
  dsimp [Ydd,T,r]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  try ring

lemma hasDerivAt_T (v : ℝ) :
    HasDerivAt T (1+theta v*Real.sinh v-1/(Real.cosh v)^2) v := by
  have hc := ne_of_gt (Real.cosh_pos v)
  convert ((hasDerivAt_theta v).mul (Real.hasDerivAt_cosh v)).sub (hasDerivAt_r v)
    using 1 <;> try rfl
  field_simp
  try ring

lemma hasDerivAt_Z (v : ℝ) : HasDerivAt Z (Zd v) v := by
  convert (((hasDerivAt_r v).const_mul (Real.pi+1)).add
    ((Real.hasDerivAt_sinh v).const_mul 2)).sub ((hasDerivAt_id v).const_mul (5*Real.pi/3))
    using 1 <;> try rfl
  dsimp [Zd]
  ring

lemma hasDerivAt_Zd (v : ℝ) : HasDerivAt Zd (Zdd v) v := by
  have hc := ne_of_gt (Real.cosh_pos v)
  convert (((hasDerivAt_const v (Real.pi+1)).div ((Real.hasDerivAt_cosh v).pow 2) (pow_ne_zero 2 hc)).add
    ((Real.hasDerivAt_cosh v).const_mul 2)).sub_const (5*Real.pi/3) using 1 <;> try rfl
  dsimp [Zdd,r]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  try ring

lemma hasDerivAt_sechWeight (v : ℝ) :
    HasDerivAt sechWeight ((1-2*r v*v)/(Real.cosh v)^2) v := by
  have hc := ne_of_gt (Real.cosh_pos v)
  convert (hasDerivAt_id v).div ((Real.hasDerivAt_cosh v).pow 2) (pow_ne_zero 2 hc)
    using 1 <;> try rfl
  dsimp [r]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  try ring


lemma c_pos {v : ℝ} (hv : 0<v) : 0<c v := by
  unfold c
  exact div_pos (sq_pos_of_pos (theta_pos hv)) (r_pos hv)

lemma r_monotone : Monotone r := by
  apply monotone_of_deriv_nonneg
  · intro v; exact (hasDerivAt_r v).differentiableAt
  · intro v; rw [(hasDerivAt_r v).deriv]; positivity

lemma lam_monotone : MonotoneOn lam (Ioi 0) := ProfileBounds.theta_div_tanh_monotone
lemma alpha_monotone : MonotoneOn alpha (Ioi 0) := ProfileBounds.theta_add_sinh_div_monotone
lemma two_lt_alpha {v : ℝ} (hv : 0<v) : 2<alpha v := ProfileBounds.two_lt_theta_add_sinh_div hv
lemma gamma_monotone : MonotoneOn gamma (Ioi 0) := by
  intro u hu v hv huv
  exact mul_le_mul (lam_monotone hu hv huv) (alpha_monotone hu hv huv)
    (alpha_pos hu).le (lam_pos hv).le

lemma beta_eq {v : ℝ} (hv : 0<v) : beta v = 2/c v*(1+1/gamma v) := by
  have hr := ne_of_gt (r_pos hv)
  have ht := ne_of_gt (theta_pos hv)
  have hg := ne_of_gt (gamma_pos hv)
  have hg1 : gamma v+1≠0 := by have := gamma_pos hv; positivity
  unfold beta eta c r at *
  field_simp

lemma beta_antitone : AntitoneOn beta (Ioi 0) := by
  intro u hu v hv huv
  rw [beta_eq hu,beta_eq hv]
  have hc := c_strictMono.monotoneOn hu hv huv
  have hg := gamma_monotone hu hv huv
  have h1 : 2/c v ≤ 2/c u := div_le_div_of_nonneg_left (by norm_num) (c_pos hu) hc
  have h2 : 1+1/gamma v ≤ 1+1/gamma u := by
    have hh := one_div_le_one_div_of_le (gamma_pos hu) hg
    linarith
  exact mul_le_mul h1 h2 (by have := gamma_pos hv; positivity) (by have := c_pos hu; positivity)

noncomputable def energyFactor (v : ℝ) : ℝ := c v/v*(3/2+1/(2*(gamma v+1)))

lemma energyFactor_antitone : AntitoneOn energyFactor (Ioi 0) := by
  intro u hu v hv huv
  have hγ := gamma_monotone hu hv huv
  have h1 := c_div_antitone hu hv huv
  have h2 : 3/2+1/(2*(gamma v+1)) ≤ 3/2+1/(2*(gamma u+1)) := by
    have hh := one_div_le_one_div_of_le (by have := gamma_pos hu; positivity : 0<2*(gamma u+1))
      (by linarith : 2*(gamma u+1) ≤ 2*(gamma v+1))
    linarith
  exact mul_le_mul h1 h2 (by have := gamma_pos hv; positivity) (div_pos (c_pos hu) hu).le

lemma energyReserve_eq_factor {v : ℝ} (hv : 0<v) :
    energyReserve v = r v*v*(energyFactor v-1) := by
  have hr := ne_of_gt (r_pos hv)
  have hn := ne_of_gt hv
  have hγ := gamma_pos hv
  have hg : gamma v+1≠0 := by positivity
  unfold energyReserve energyFactor eta c r at *
  field_simp
  ring

lemma Y_eq_gamma {v : ℝ} (hv : 0<v) : Y v/v=gamma v-r v*v-6/5 := by
  have hc := ne_of_gt (Real.cosh_pos v)
  have hs := ne_of_gt (Real.sinh_pos_iff.mpr hv)
  have hvn := ne_of_gt hv
  unfold Y gamma lam alpha c r
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

lemma T_pos {v : ℝ} (hv : 0<v) : 0<T v := by
  have ht := tanh_lt_theta hv
  have hc := Real.one_lt_cosh.mpr (ne_of_gt hv)
  have hθ := theta_pos hv
  unfold T r
  nlinarith

lemma T_monotone : MonotoneOn T (Ioi 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi _)
  · intro v hv; exact (hasDerivAt_T v).continuousAt.continuousWithinAt
  · intro v hv; exact (hasDerivAt_T v).differentiableAt.differentiableWithinAt
  · intro v hv
    rw [interior_Ioi] at hv
    rw [(hasDerivAt_T v).deriv]
    have hc := Real.one_le_cosh v
    have hq : 1/(Real.cosh v)^2 ≤ 1 := (div_le_one (sq_pos_of_pos (Real.cosh_pos v))).mpr (by nlinarith)
    have hprod := _root_.mul_nonneg (theta_pos hv).le (Real.sinh_pos_iff.mpr hv).le
    linarith

lemma cosh_mono_nonneg {u v : ℝ} (hu : 0≤u) (huv : u≤v) : Real.cosh u≤Real.cosh v := by
  exact Real.cosh_le_cosh.mpr (by simpa only [abs_of_nonneg hu,abs_of_nonneg (hu.trans huv)] using huv)

lemma sechWeight_antitone {a : ℝ} (ha : 0<a) (har : 1≤2*r a*a) :
    AntitoneOn sechWeight (Ici a) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · intro v hv; exact (hasDerivAt_sechWeight v).continuousAt.continuousWithinAt
  · intro v hv; exact (hasDerivAt_sechWeight v).differentiableAt.differentiableWithinAt
  · intro v hv
    have hav : a≤v := interior_subset hv
    have hr := r_monotone hav
    have hp := mul_le_mul hr hav ha.le (r_pos (ha.trans_le hav)).le
    rw [(hasDerivAt_sechWeight v).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)

/-- A symbolic lower bound for the curvature of Y, propagated from one endpoint. -/
noncomputable def curvatureFloor (a : ℝ) : ℝ :=
  T a*(1-2/(Real.sinh a)^2)+2*sechWeight a*(r a*a-2)

lemma Ydd_ge_endpoint {a v : ℝ} (ha : 0<a) (hav : a≤v)
    (har : 1≤2*r a*a) (har2 : r a*a≤2) (hs2 : 2≤(Real.sinh a)^2) :
    curvatureFloor a ≤ Ydd v := by
  have hv := ha.trans_le hav
  have hsa := Real.sinh_pos_iff.mpr ha
  have hsv := Real.sinh_pos_iff.mpr hv
  have hsav := Real.sinh_le_sinh.mpr hav
  have hss : (Real.sinh a)^2 ≤ (Real.sinh v)^2 := pow_le_pow_left₀ hsa.le hsav 2
  have hsden := sq_pos_of_pos hsa
  have hvden := sq_pos_of_pos hsv
  have hfrac : 2/(Real.sinh v)^2 ≤ 2/(Real.sinh a)^2 :=
    div_le_div_of_nonneg_left (by norm_num) hsden hss
  have hsave : 0≤s v := (s_pos hv).le
  have hfrac' : 2*(1-s v)/(Real.sinh v)^2 ≤ 2/(Real.sinh v)^2 :=
    div_le_div_of_nonneg_right (by linarith) hvden.le
  have hb : 1-2/(Real.sinh a)^2 ≤ 1-2*(1-s v)/(Real.sinh v)^2 := by linarith
  have hb0 : 0≤1-2/(Real.sinh a)^2 := by
    have := (div_le_one hsden).mpr hs2
    linarith
  have hT := T_monotone ha hv hav
  have hmain := mul_le_mul hT hb hb0 (T_pos hv).le
  have hA := sechWeight_antitone ha har (by simp : a∈Ici a) hav hav
  have hA0 : 0≤sechWeight v := div_nonneg hv.le (sq_nonneg _)
  have hB : r a*a-2 ≤ r v*v-2 := by
    have hh := mul_le_mul (r_monotone hav) hav ha.le (r_pos hv).le
    linarith
  have hB0 : r a*a-2 ≤ 0 := by linarith
  have hlow := mul_le_mul_of_nonpos_right hA hB0
  have hupper := mul_le_mul_of_nonneg_left hB hA0
  have hh := add_le_add hmain (mul_le_mul_of_nonneg_left (hlow.trans hupper) (by norm_num : 0≤(2:ℝ)))
  convert hh using 1 <;> try rfl
  all_goals dsimp [curvatureFloor,Ydd,sechWeight]; ring

lemma Zdd_pos_of_endpoint {a v : ℝ} (ha : 0<a) (hav : a≤v)
    (hcheck : Real.pi+1<Real.sinh a*(Real.cosh a)^2) : 0<Zdd v := by
  have hv := ha.trans_le hav
  have hca := Real.cosh_pos a
  have hcv := Real.cosh_pos v
  have hc := cosh_mono_nonneg ha.le hav
  have hsq := pow_le_pow_left₀ hca.le hc 2
  have hs := Real.sinh_le_sinh.mpr hav
  have hrate : r v≤1 := (Real.tanh_lt_one v).le
  have hr0 := (r_pos hv).le
  have hpi := Real.pi_pos
  have hfrac1 : (Real.pi+1)*r v/(Real.cosh v)^2 ≤ (Real.pi+1)/(Real.cosh v)^2 :=
    div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg _)
  have hfrac2 : (Real.pi+1)/(Real.cosh v)^2 ≤ (Real.pi+1)/(Real.cosh a)^2 :=
    div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hca) hsq
  have hfrac3 : (Real.pi+1)/(Real.cosh a)^2 < Real.sinh a :=
    (div_lt_iff₀ (sq_pos_of_pos hca)).mpr hcheck
  have hh := (hfrac1.trans_lt (hfrac2.trans_lt hfrac3)).trans_le hs
  unfold Zdd
  ring_nf at hh ⊢
  linarith


lemma r_enclosure {v lo hi : ℝ} (he : Encloses (Real.exp v) lo hi) (hl : 0≤lo) :
    Encloses (r v) (1-2/(lo^2+1)) (1-2/(hi^2+1)) := by
  rw [r_exp]
  exact sub (exact_value 1) (div_nonneg (exact_value 2)
    (add (pow_nonneg he hl 2) (exact_value 1)) (by norm_num) (by positivity))

lemma sinh_enclosure {v lo hi : ℝ} (he : Encloses (Real.exp v) lo hi) (hl : 0<lo) :
    Encloses (Real.sinh v) ((lo-1/lo)/2) ((hi-1/hi)/2) := by
  have hh := inv_pos he hl
  rw [sinh_exp]
  constructor <;> linarith [he.1,he.2,hh.1,hh.2]

lemma cosh_enclosure {v lo hi : ℝ} (he : Encloses (Real.exp v) lo hi) (hl : 0<lo) :
    Encloses (Real.cosh v) ((lo+1/hi)/2) ((hi+1/lo)/2) := by
  have hh := inv_pos he hl
  rw [Real.cosh_eq,Real.exp_neg]
  simp only [one_div] at hh ⊢
  constructor <;> linarith [he.1,he.2,hh.1,hh.2]

/-- Coarse rational pi brackets suffice for every new fixed-parameter check. -/
lemma theta_simple_enclosure {v lo hi : ℝ} (hv : 0≤v) (hl : 0<lo)
    (he : Encloses (Real.exp v) lo hi) :
    Encloses (theta v) (157/100-2/lo) (11/7-2/hi+2/(3*lo^3)) := by
  have hp : Encloses Real.pi (157/50) (22/7) := by
    constructor <;> linarith [Real.pi_gt_d6,Real.pi_lt_d6]
  convert theta_enclosure_of_pi hv hl he hp using 1 <;> norm_num

private lemma exp_mean_point : Encloses (Real.exp (3/2:ℝ)) (112/25) (9/2) := by
  have hl := Real.sum_le_exp_of_nonneg (by norm_num : 0≤(3/8:ℝ)) 12
  have hu := Real.exp_bound' (by norm_num : 0≤(3/8:ℝ)) (by norm_num : (3/8:ℝ)≤1) (by norm_num : 0<(12:ℕ))
  norm_num [Finset.sum_range_succ,Nat.factorial] at hl hu
  have he : Encloses (Real.exp (3/8:ℝ)) (14549/10000) (14551/10000) := by constructor <;> linarith
  rw [show (3/2:ℝ)=(4:ℕ)*(3/8) by norm_num,Real.exp_nat_mul]
  exact weaken (pow_nonneg he (by norm_num) 4) (by norm_num) (by norm_num)

private lemma exp_start_point : Encloses (Real.exp (31/20:ℝ)) (47/10) (24/5) := by
  have hl := Real.sum_le_exp_of_nonneg (by norm_num : 0≤(31/80:ℝ)) 12
  have hu := Real.exp_bound' (by norm_num : 0≤(31/80:ℝ)) (by norm_num : (31/80:ℝ)≤1) (by norm_num : 0<(12:ℕ))
  norm_num [Finset.sum_range_succ,Nat.factorial] at hl hu
  have he : Encloses (Real.exp (31/80:ℝ)) (1473/1000) (737/500) := by constructor <;> linarith
  rw [show (31/20:ℝ)=(4:ℕ)*(31/80) by norm_num,Real.exp_nat_mul]
  exact weaken (pow_nonneg he (by norm_num) 4) (by norm_num) (by norm_num)

private lemma exp_two_point : Encloses (Real.exp (2:ℝ)) (369/50) (37/5) := by
  have hl := Real.sum_le_exp_of_nonneg (by norm_num : 0≤(1/2:ℝ)) 12
  have hu := Real.exp_bound' (by norm_num : 0≤(1/2:ℝ)) (by norm_num : (1/2:ℝ)≤1) (by norm_num : 0<(12:ℕ))
  norm_num [Finset.sum_range_succ,Nat.factorial] at hl hu
  have he : Encloses (Real.exp (1/2:ℝ)) (3297/2000) (1649/1000) := by constructor <;> linarith
  rw [show (2:ℝ)=(4:ℕ)*(1/2) by norm_num,Real.exp_nat_mul]
  exact weaken (pow_nonneg he (by norm_num) 4) (by norm_num) (by norm_num)

private lemma exp_end_point : Encloses (Real.exp (7/2:ℝ)) 33 34 := by
  have hl := Real.sum_le_exp_of_nonneg (by norm_num : 0≤(7/8:ℝ)) 12
  have hu := Real.exp_bound' (by norm_num : 0≤(7/8:ℝ)) (by norm_num : (7/8:ℝ)≤1) (by norm_num : 0<(12:ℕ))
  norm_num [Finset.sum_range_succ,Nat.factorial] at hl hu
  have he : Encloses (Real.exp (7/8:ℝ)) (1199/500) (2399/1000) := by constructor <;> linarith
  rw [show (7/2:ℝ)=(4:ℕ)*(7/8) by norm_num,Real.exp_nat_mul]
  exact weaken (pow_nonneg he (by norm_num) 4) (by norm_num) (by norm_num)

lemma beta_at_start : beta (31/20)<2 := by
  have he := exp_start_point
  have ht := theta_simple_enclosure (by norm_num : 0≤(31/20:ℝ)) (by norm_num) he
  have hr := r_enclosure he (by norm_num)
  have hs := sinh_enclosure he (by norm_num)
  have hl := div_nonneg ht hr (by norm_num) (by norm_num)
  have ha := div_nonneg (add ht hs) (exact_value (31/20:ℝ)) (by norm_num) (by norm_num)
  have hg := mul_nonneg hl ha (by norm_num) (by norm_num)
  have heta := mul_nonneg (pow_nonneg ht (by norm_num) 2) (unit_fraction_enclosure hg (by norm_num))
    (by norm_num) (by norm_num)
  have hb := div_nonneg (mul_nonneg (exact_value 2) hr (by norm_num) (by norm_num)) heta
    (by norm_num) (by norm_num)
  change Encloses (beta (31/20)) _ _ at hb
  exact lt_of_le_of_lt hb.2 (by norm_num)

lemma beta_at_two : beta 2<3/2 := by
  have he := exp_two_point
  have ht := theta_simple_enclosure (by norm_num : 0≤(2:ℝ)) (by norm_num) he
  have hr := r_enclosure he (by norm_num)
  have hs := sinh_enclosure he (by norm_num)
  have hl := div_nonneg ht hr (by norm_num) (by norm_num)
  have ha := div_nonneg (add ht hs) (exact_value (2:ℝ)) (by norm_num) (by norm_num)
  have hg := mul_nonneg hl ha (by norm_num) (by norm_num)
  have heta := mul_nonneg (pow_nonneg ht (by norm_num) 2) (unit_fraction_enclosure hg (by norm_num))
    (by norm_num) (by norm_num)
  have hb := div_nonneg (mul_nonneg (exact_value 2) hr (by norm_num) (by norm_num)) heta
    (by norm_num) (by norm_num)
  change Encloses (beta 2) _ _ at hb
  exact lt_of_le_of_lt hb.2 (by norm_num)

lemma energyFactor_at_end : 1<energyFactor (7/2) := by
  have he := exp_end_point
  have ht := theta_simple_enclosure (by norm_num : 0≤(7/2:ℝ)) (by norm_num) he
  have hr := r_enclosure he (by norm_num)
  have hs := sinh_enclosure he (by norm_num)
  have hl := div_nonneg ht hr (by norm_num) (by norm_num)
  have ha := div_nonneg (add ht hs) (exact_value (7/2:ℝ)) (by norm_num) (by norm_num)
  have hg := mul_nonneg hl ha (by norm_num) (by norm_num)
  have hγ := inv_pos (mul_nonneg (exact_value 2) (add hg (exact_value 1)) (by norm_num) (by norm_num)) (by norm_num)
  have hc := div_nonneg (pow_nonneg ht (by norm_num) 2) hr (by norm_num) (by norm_num)
  have hcv := div_nonneg hc (exact_value (7/2:ℝ)) (by norm_num) (by norm_num)
  have hh := mul_nonneg hcv (add (exact_value (3/2:ℝ)) hγ) (by norm_num) (by norm_num)
  change Encloses (energyFactor (7/2)) _ _ at hh
  exact lt_of_lt_of_le (by norm_num) hh.1


lemma mean_start_geometry :
    1≤2*r (3/2)*(3/2) ∧ r (3/2)*(3/2)≤2 ∧ 2≤(Real.sinh (3/2))^2 := by
  have hr := r_enclosure exp_mean_point (by norm_num)
  have hs := pow_nonneg (sinh_enclosure exp_mean_point (by norm_num)) (by norm_num) 2
  constructor
  · linarith [hr.1]
  constructor
  · linarith [hr.2]
  · exact le_trans (by norm_num) hs.1

lemma mean_start_curvature : 1/2<curvatureFloor (3/2) := by
  have ht := theta_simple_enclosure (by norm_num : 0≤(3/2:ℝ)) (by norm_num) exp_mean_point
  have hr := r_enclosure exp_mean_point (by norm_num)
  have hs := sinh_enclosure exp_mean_point (by norm_num)
  have hc := cosh_enclosure exp_mean_point (by norm_num)
  have hT := sub (mul_nonneg ht hc (by norm_num) (by norm_num)) hr
  have hbr := sub (exact_value 1) (div_nonneg (exact_value 2)
    (pow_nonneg hs (by norm_num) 2) (by norm_num) (by norm_num))
  have hA := div_nonneg (exact_value (3/2:ℝ)) (pow_nonneg hc (by norm_num) 2) (by norm_num) (by norm_num)
  have hB := sub (exact_value 2) (mul_nonneg hr (exact_value (3/2:ℝ)) (by norm_num) (by norm_num))
  have hmain := mul_nonneg hT hbr (by norm_num) (by norm_num)
  have htail := mul_nonneg (mul_nonneg (exact_value 2) hA (by norm_num) (by norm_num)) hB (by norm_num) (by norm_num)
  have hh := sub hmain htail
  have hid : curvatureFloor (3/2) =
      (theta (3/2)*Real.cosh (3/2)-r (3/2))*(1-2/(Real.sinh (3/2))^2)-
      (2*((3/2)/(Real.cosh (3/2))^2))*(2-r (3/2)*(3/2)) := by
    unfold curvatureFloor T sechWeight
    ring
  rw [hid]
  exact lt_of_lt_of_le (by norm_num) hh.1

lemma mean_start_discriminant : (Yd (3/2))^2<Y (3/2) := by
  have ht := theta_simple_enclosure (by norm_num : 0≤(3/2:ℝ)) (by norm_num) exp_mean_point
  have hr := r_enclosure exp_mean_point (by norm_num)
  have hs := sinh_enclosure exp_mean_point (by norm_num)
  have hc := cosh_enclosure exp_mean_point (by norm_num)
  have hcprof := div_nonneg (pow_nonneg ht (by norm_num) 2) hr (by norm_num) (by norm_num)
  have hY := sub (sub (add hcprof (mul_nonneg ht hc (by norm_num) (by norm_num)))
    (mul_nonneg hr (exact_value ((3/2:ℝ)^2)) (by norm_num) (by norm_num))) (exact_value (6*(3/2:ℝ)/5))
  change Encloses (Y (3/2)) _ _ at hY
  have hsrat := div_nonneg ht hs (by norm_num) (by norm_num)
  have hcd := sub (mul_nonneg (exact_value 2) hsrat (by norm_num) (by norm_num))
    (pow_nonneg hsrat (by norm_num) 2)
  have hd := sub (sub (sub (add (add hcd (exact_value 1)) (mul_nonneg ht hs (by norm_num) (by norm_num)))
    (div_nonneg (exact_value ((3/2:ℝ)^2)) (pow_nonneg hc (by norm_num) 2) (by norm_num) (by norm_num)))
    (mul_nonneg (mul_nonneg (exact_value 2) hr (by norm_num) (by norm_num)) (exact_value (3/2:ℝ))
      (by norm_num) (by norm_num))) (exact_value (6/5:ℝ))
  change Encloses (Yd (3/2)) _ _ at hd
  have hd2 := pow_nonneg (neg hd) (by norm_num) 2
  rw [neg_sq] at hd2
  exact lt_of_le_of_lt hd2.2 (lt_of_lt_of_le (by norm_num) hY.1)

lemma mean_start_small_cost : 2*(s (3/2))^2<3/5 := by
  have ht := theta_simple_enclosure (by norm_num : 0≤(3/2:ℝ)) (by norm_num) exp_mean_point
  have hs := sinh_enclosure exp_mean_point (by norm_num)
  have hsrat := div_nonneg ht hs (by norm_num) (by norm_num)
  have hh := mul_nonneg (exact_value 2) (pow_nonneg hsrat (by norm_num) 2) (by norm_num) (by norm_num)
  exact lt_of_le_of_lt hh.2 (by norm_num)

lemma Z_start_checks :
    Real.pi+1<Real.sinh (3/2)*(Real.cosh (3/2))^2 ∧ 0<Zd (3/2) ∧ 0<Z (3/2) := by
  have hr := r_enclosure exp_mean_point (by norm_num)
  have hs := sinh_enclosure exp_mean_point (by norm_num)
  have hc := cosh_enclosure exp_mean_point (by norm_num)
  have hp : Encloses Real.pi (157/50) (22/7) := by constructor <;> linarith [Real.pi_gt_d6,Real.pi_lt_d6]
  have hc2 := pow_nonneg hc (by norm_num) 2
  have hsc2 := mul_nonneg hs hc2 (by norm_num) (by norm_num)
  have hpp := add hp (exact_value 1)
  have hcost := div_nonneg (mul_nonneg (exact_value 5) hp (by norm_num) (by norm_num))
    (exact_value 3) (by norm_num) (by norm_num)
  have hZd := sub (add (div_nonneg hpp hc2 (by norm_num) (by norm_num))
    (mul_nonneg (exact_value 2) hc (by norm_num) (by norm_num))) hcost
  have hZ := sub (add (mul_nonneg hpp hr (by norm_num) (by norm_num))
    (mul_nonneg (exact_value 2) hs (by norm_num) (by norm_num)))
    (mul_nonneg hcost (exact_value (3/2:ℝ)) (by norm_num) (by norm_num))
  refine ⟨?_,lt_of_lt_of_le (by norm_num) hZd.1,lt_of_lt_of_le (by norm_num) hZ.1⟩
  exact lt_of_le_of_lt hpp.2 (lt_of_lt_of_le (by norm_num) hsc2.1)


/-- The main mean-budget gap is positive on the entire half-line. -/
lemma Y_pos {v : ℝ} (hv : 3/2≤v) : 0<Y v := by
  have ha : (0:ℝ)<3/2 := by norm_num
  have hg := mean_start_geometry
  have hq := quadratic_lower_of_second_derivative
    (a := (3/2:ℝ)) (κ := (1/2:ℝ)) (x := v)
    (fun t ht => hasDerivAt_Y (ha.trans_le ht))
    (fun t ht => hasDerivAt_Yd (ha.trans_le ht))
    (fun t ht => mean_start_curvature.le.trans (Ydd_ge_endpoint ha ht hg.1 hg.2.1 hg.2.2)) hv
  have hdisc := mean_start_discriminant
  have hsq := sq_nonneg ((v-3/2)/2+Yd (3/2))
  nlinarith

lemma Z_pos {v : ℝ} (hv : 3/2≤v) : 0<Z v := by
  have hz := Z_start_checks
  have hq := quadratic_lower_of_second_derivative
    (a := (3/2:ℝ)) (κ := (0:ℝ)) (x := v)
    (fun t _ => hasDerivAt_Z t) (fun t _ => hasDerivAt_Zd t)
    (fun t ht => (Zdd_pos_of_endpoint (by norm_num) ht hz.1).le) hv
  have hp := _root_.mul_nonneg hz.2.1.le (sub_nonneg.mpr hv)
  nlinarith [hz.2.2]

lemma theta_upper_cosh {v : ℝ} (hv : 0<v) :
    theta v*(2*Real.cosh v+1) ≤ Real.pi*Real.sinh v := by
  have hc := Real.cosh_pos v
  have hh := (arcsin_brackets ⟨(r_pos hv).le,(Real.tanh_lt_one v).le⟩).2
  have hr : Real.sqrt (1-(Real.tanh v)^2)=1/Real.cosh v := by
    rw [cosh_eq_inv_sqrt,one_div_div,div_one]
  unfold r at hh
  rw [hr,Real.tanh_eq_sinh_div_cosh] at hh
  have hid : Real.pi*(Real.sinh v/Real.cosh v)/(2+1/Real.cosh v)=
      Real.pi*Real.sinh v/(2*Real.cosh v+1) := by field_simp
  rw [hid,← Real.tanh_eq_sinh_div_cosh v] at hh
  exact (le_div_iff₀ (by positivity : 0<2*Real.cosh v+1)).mp hh

lemma lam_div_alpha_upper {v : ℝ} (hv : 0<v) :
    lam v/alpha v ≤ Real.pi*v/((Real.pi+1)*r v+2*Real.sinh v) := by
  have hθ := theta_pos hv
  have hS := Real.sinh_pos_iff.mpr hv
  have hR := r_pos hv
  have hC := Real.cosh_pos v
  have hπ := Real.pi_pos
  have hθS : 0<theta v+Real.sinh v := add_pos hθ hS
  have hD : 0<(Real.pi+1)*r v+2*Real.sinh v := by positivity
  have hrC : r v*Real.cosh v=Real.sinh v := by
    unfold r
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
  have hm := mul_le_mul_of_nonneg_left (theta_upper_cosh hv) hR.le
  have he := congrArg (fun z : ℝ => 2*theta v*z) hrC
  have hb : theta v*((Real.pi+1)*r v+2*Real.sinh v) ≤ Real.pi*r v*(theta v+Real.sinh v) := by
    nlinarith only [hm,he]
  have hh := mul_le_mul_of_nonneg_left hb hv.le
  have hid : lam v/alpha v = v*theta v/(r v*(theta v+Real.sinh v)) := by
    unfold lam alpha
    field_simp
  rw [hid,div_le_div_iff₀ (mul_pos hR hθS) hD]
  nlinarith only [hh]

lemma lam_div_alpha_lt {v : ℝ} (hv : 3/2≤v) : lam v/alpha v<3/5 := by
  have hv0 : 0<v := by linarith
  have hR := r_pos hv0
  have hS := Real.sinh_pos_iff.mpr hv0
  have hπ := Real.pi_pos
  have hD : 0<(Real.pi+1)*r v+2*Real.sinh v := by positivity
  apply lt_of_le_of_lt (lam_div_alpha_upper hv0)
  apply (div_lt_iff₀ hD).mpr
  have hh := Z_pos hv
  unfold Z at hh
  nlinarith

lemma meanReserve_pos {v : ℝ} (hv : 3/2≤v) : 0<meanReserve v := by
  have hv0 : 0<v := by linarith
  have hy := div_pos (Y_pos hv) hv0
  rw [Y_eq_gamma hv0] at hy
  have hs := ProfileBounds.s_antitone (by norm_num : (3/2:ℝ)∈Ioi 0) hv0 hv
  have hs2 := pow_le_pow_left₀ (s_pos hv0).le hs 2
  have hcost : 2*(s v)^2<3/5 := by nlinarith [mean_start_small_cost]
  have hratio := lam_div_alpha_lt hv
  have hid : 2*(theta v)^2/(Real.sinh v)^2=2*(s v)^2 := by unfold s; ring
  unfold meanReserve
  rw [hid]
  linarith

lemma beta_le_two {v : ℝ} (hv : 31/20≤v) : beta v≤2 := by
  exact (beta_antitone (by norm_num : (31/20:ℝ)∈Ioi 0) (by change 0<v; linarith : v∈Ioi 0) hv).trans beta_at_start.le

lemma beta_le_three_halves {v : ℝ} (hv : 2≤v) : beta v≤3/2 := by
  exact (beta_antitone (by norm_num : (2:ℝ)∈Ioi 0) (by change 0<v; linarith : v∈Ioi 0) hv).trans beta_at_two.le

lemma energyReserve_nonneg {v : ℝ} (hv : v∈Ioc 0 (7/2)) : 0≤energyReserve v := by
  have hp := energyFactor_antitone hv.1 (by norm_num : (7/2:ℝ)∈Ioi 0) hv.2
  rw [energyReserve_eq_factor hv.1]
  exact _root_.mul_nonneg (mul_pos (r_pos hv.1) hv.1).le (by linarith [energyFactor_at_end])

/-- Compatibility wrapper for the lower part of the original middle interval. -/
theorem small_reserves {ell : ℝ} (hel : ell ∈ Icc ((31:ℝ)/20) (2:ℝ)) :
    beta ell ≤ (2:ℝ) ∧ 0 ≤ energyReserve ell ∧ 0 ≤ meanReserve ell := by
  refine ⟨beta_le_two hel.1,energyReserve_nonneg ⟨by linarith [hel.1],by linarith [hel.2]⟩,?_⟩
  exact (meanReserve_pos (by linarith [hel.1])).le

/-- Compatibility wrapper for the upper part of the original middle interval. -/
theorem large_reserves {ell : ℝ} (hel : ell ∈ Icc (2:ℝ) ((7:ℝ)/2)) :
    beta ell ≤ ((3:ℝ)/2) ∧ 0 ≤ energyReserve ell ∧ 0 ≤ meanReserve ell := by
  refine ⟨beta_le_three_halves hel.1,energyReserve_nonneg ⟨by linarith [hel.1],hel.2⟩,?_⟩
  exact (meanReserve_pos (by linarith [hel.1])).le

lemma hasDerivAt_log_vF {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun v => Real.log (v*F v)) (1/v-rate v) v := by
  have hf : HasDerivAt F (deriv F v) v := (hasDerivAt_F hv).differentiableAt.hasDerivAt
  convert ((hasDerivAt_id v).mul hf).log (ne_of_gt (mul_pos hv (F_pos hv))) using 1 <;> try rfl
  dsimp
  unfold rate
  have hfn := ne_of_gt (F_pos hv)
  field_simp
  ring

lemma hasDerivAt_H {v : ℝ} (hv : 0 < v) : HasDerivAt H (1-cd v) v :=
  (hasDerivAt_id v).sub (hasDerivAt_c hv)

/-- Integrates a pointwise profile rate. The hypothesis is discharged below. -/
lemma profile_reduction {ell b : ℝ} (hell : 0 < ell)
    (hbound : ∀ v ∈ Ioc (0:ℝ) ell, b*(1-cd v) ≤ rate v-1/v)
    {v : ℝ} (hv : v ∈ Ioc (0:ℝ) ell) :
    b*(H ell-H v) ≤ Real.log ((v*F v)/(ell*F ell)) := by
  let f : ℝ → ℝ := fun v => Real.log (v*F v)+b*H v
  have hd (v : ℝ) (hv : 0 < v) : HasDerivAt f
      (1/v-rate v+b*(1-cd v)) v :=
    (hasDerivAt_log_vF hv).add ((hasDerivAt_H hv).const_mul b)
  have hm : AntitoneOn f (Icc v ell) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · intro x hx
      exact (hd x (lt_of_lt_of_le hv.1 hx.1)).continuousAt.continuousWithinAt
    · intro x hx
      have hx' := interior_subset hx
      exact (hd x (lt_of_lt_of_le hv.1 hx'.1)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' := interior_subset hx
      rw [(hd x (lt_of_lt_of_le hv.1 hx'.1)).deriv]
      have hh := hbound x ⟨lt_of_lt_of_le hv.1 hx'.1, hx'.2⟩
      linarith
  have hh := hm ⟨le_rfl,hv.2⟩ ⟨hv.2,le_rfl⟩ hv.2
  rw [Real.log_div (ne_of_gt (mul_pos hv.1 (F_pos hv.1)))
    (ne_of_gt (mul_pos hell (F_pos hell)))]
  dsimp [f] at hh
  linarith

/-- The actual middle-range profile inequality, with no analytic assumptions. -/
theorem middle_profile {ell v : ℝ} (hell : ell ∈ Icc ((31:ℝ)/20) ((7:ℝ)/2))
    (hv : v ∈ Ioc (0:ℝ) ell) :
    beta ell*(H ell-H v) ≤ Real.log ((v*F v)/(ell*F ell)) := by
  apply profile_reduction (by linarith [hell.1]) ?_ hv
  intro x hx
  have hn : 0 ≤ 1-cd x := by rw [one_sub_cd]; positivity
  by_cases he : ell ≤ 2
  · have hb := (small_reserves ⟨hell.1,he⟩).1
    have hh := rate_angle_two (show x ∈ Ioc (0:ℝ) 2 from ⟨hx.1,hx.2.trans he⟩)
    rw [(hasDerivAt_c hx.1).deriv] at hh
    exact (mul_le_mul_of_nonneg_right hb hn).trans hh.le
  · have hb := (large_reserves ⟨by linarith,hell.2⟩).1
    have hh := rate_angle_three_halves hx.1
    rw [(hasDerivAt_c hx.1).deriv] at hh
    exact (mul_le_mul_of_nonneg_right hb hn).trans hh.le

theorem middle_energy {ell : ℝ} (hell : ell ∈ Icc ((31:ℝ)/20) ((7:ℝ)/2)) :
    0 ≤ (theta ell)^2-r ell*H ell-eta ell/2 := by
  have he : 0 ≤ energyReserve ell := by
    by_cases hh : ell ≤ 2
    · exact (small_reserves ⟨hell.1,hh⟩).2.1
    · exact (large_reserves ⟨by linarith,hell.2⟩).2.1
  have hr := ne_of_gt (r_pos (show 0 < ell by linarith [hell.1]))
  have hid : r ell*c ell = (theta ell)^2 := by
    unfold c r at *
    field_simp
  unfold H energyReserve at *
  nlinarith

theorem middle_mean {ell : ℝ} (hell : ell ∈ Icc ((31:ℝ)/20) ((7:ℝ)/2)) :
    r ell*ell ≤ gamma ell-2*(theta ell)^2/(Real.sinh ell)^2-lam ell/alpha ell := by
  have he : 0 ≤ meanReserve ell := by
    by_cases hh : ell ≤ 2
    · exact (small_reserves ⟨hell.1,hh⟩).2.2
    · exact (large_reserves ⟨by linarith,hell.2⟩).2.2
  exact sub_nonneg.mp he

/-- All three conclusions of Lemma `middle-channel-checks` from the manuscript. -/
theorem middle_channel_checks {ell : ℝ}
    (hell : ell ∈ Icc ((31:ℝ)/20) ((7:ℝ)/2)) :
    (∀ v ∈ Ioc (0:ℝ) ell, beta ell*(H ell-H v) ≤ Real.log ((v*F v)/(ell*F ell))) ∧
    0 ≤ (theta ell)^2-r ell*H ell-eta ell/2 ∧
    r ell*ell ≤ gamma ell-2*(theta ell)^2/(Real.sinh ell)^2-lam ell/alpha ell :=
  ⟨fun _ hv => middle_profile hell hv,middle_energy hell,middle_mean hell⟩

end MostInformativeBit.MiddleChannel
