import MostInformativeBit.Definitions
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Scalar analytic ingredients for `centered-support.tex`.
All results with unproved analytic premises are explicitly named `reduction`.
-/
namespace MostInformativeBit.CenteredSupport
open Set Real

/-- Log odds, on the natural open interval. -/
noncomputable def g (x : ℝ) : ℝ := (Real.log (1+x) - Real.log (1-x))/2

lemma g_eq_artanh {x : ℝ} (hx : x ∈ Ioo (-1) 1) : g x = Real.artanh x := by
  rw [Real.artanh_eq_half_log (Ioo_subset_Icc_self hx),
    Real.log_div (by linarith [hx.1]) (by linarith [hx.2])]
  unfold g
  ring

lemma hasDerivAt_g {x : ℝ} (hx : x ∈ Ioo (-1) 1) :
    HasDerivAt g (1 / (1-x^2)) x := by
  have hp : 1+x ≠ 0 := by linarith [hx.1]
  have hm : 1-x ≠ 0 := by linarith [hx.2]
  have hh := ((((hasDerivAt_id x).const_add 1).log hp).sub
    (((hasDerivAt_id x).const_sub 1).log hm)).div_const 2
  convert hh using 1 <;> try rfl
  dsimp
  field_simp [hp, hm, show 1-x^2 ≠ 0 by nlinarith [hx.1, hx.2]]
  ring

lemma hasDerivAt_phi {x : ℝ} (hx : x ∈ Ioo (-1) 1) :
    HasDerivAt phi (g x) x := by
  have hp : (1-x)/2 ≠ 0 := by linarith [hx.2]
  have hm : (1-x)/2 ≠ 1 := by linarith [hx.1]
  have hh := ((Real.hasDerivAt_binEntropy hp hm).comp x
    (((hasDerivAt_id x).const_sub 1).div_const 2)).const_sub (Real.log 2)
  convert hh using 1 <;> try rfl
  dsimp only [g]
  rw [show 1-(1-x)/2 = (1+x)/2 by ring,
      Real.log_div (by linarith [hx.1]) (by norm_num),
      Real.log_div (by linarith [hx.2]) (by norm_num)]
  ring

lemma phi_even (x : ℝ) : phi (-x) = phi x := by
  unfold phi h
  rw [show (1- -x)/2 = 1-(1-x)/2 by ring, Real.binEntropy_one_sub]

lemma continuous_phi : Continuous phi := by unfold phi h; fun_prop

/-- The polynomial certificate printed in the manuscript. -/
def Q (c : ℝ) : ℝ :=
  375*(2-6*c-7*c^2)^2 + 164*(1-c)^5 + 740*c*(1-c)^4 +
  c^2*(1-c)^3 + 25*c^3*(1-c)^2 + 5925*c^4*(1-c) + 8625*c^5

lemma Q_pos {c : ℝ} (hc : c ∈ Icc 0 1) : 0 < Q c := by
  have hn : 0 ≤ 1-c := by linarith [hc.2]
  by_cases hz : c = 0
  · norm_num [Q, hz]
  · have hp : 0 < c := lt_of_le_of_ne hc.1 (Ne.symm hz)
    unfold Q
    positivity

/-- Padé upper bound used in the half-angle substitution. -/
lemma arctan_le_rational {y : ℝ} (hy : 0 ≤ y) :
    Real.arctan y ≤ y*(15+4*y^2)/(15+9*y^2) := by
  let f : ℝ → ℝ := fun z => z*(15+4*z^2)/(15+9*z^2)-Real.arctan z
  have hd (z : ℝ) : HasDerivAt f
      (36*z^6/((15+9*z^2)^2*(1+z^2))) z := by
    have hn : 15+9*z^2 ≠ 0 := by positivity
    have hn' : 1+z^2 ≠ 0 := by positivity
    convert (((hasDerivAt_id z).mul ((hasDerivAt_const z 15).add
      (((hasDerivAt_id z).pow 2).const_mul 4))).div
      ((hasDerivAt_const z 15).add (((hasDerivAt_id z).pow 2).const_mul 9)) hn).sub
      (Real.hasDerivAt_arctan z) using 1 <;> try rfl
    dsimp
    field_simp [hn, hn']
    ring
  have hm : Monotone f := monotone_of_hasDerivAt_nonneg hd (fun z => by positivity)
  have := hm hy
  dsimp [f] at this
  simpa using this

/-- Padé lower bound for artanh; the endpoint 1 is excluded. -/
lemma artanh_ge_rational {y : ℝ} (hy : y ∈ Ico 0 1) :
    y*(15-4*y^2)/(15-9*y^2) ≤ Real.artanh y := by
  let f : ℝ → ℝ := fun z => g z-z*(15-4*z^2)/(15-9*z^2)
  have hd (z : ℝ) (hz : z ∈ Ioo (-1) 1) : HasDerivAt f
      (36*z^6/((15-9*z^2)^2*(1-z^2))) z := by
    have hz2 : z^2 < 1 := by nlinarith [hz.1, hz.2]
    have hn : 15-9*z^2 ≠ 0 := by linarith
    have hn' : 1-z^2 ≠ 0 := by linarith
    have hn2 : (15-9*z^2)^2 ≠ 0 := pow_ne_zero 2 hn
    convert (hasDerivAt_g hz).sub
      (((hasDerivAt_id z).mul ((hasDerivAt_const z 15).sub
      (((hasDerivAt_id z).pow 2).const_mul 4))).div
      ((hasDerivAt_const z 15).sub (((hasDerivAt_id z).pow 2).const_mul 9)) hn)
      using 1 <;> try rfl
    dsimp
    field_simp [hn, hn', hn2]
    ring_nf
    have hn3 : 225-z^2*270+z^4*81 ≠ 0 := by
      nlinarith [sq_pos_of_ne_zero hn]
    field_simp [hn3]
    ring
  have hm : MonotoneOn f (Ico 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
    · intro z hz
      exact (hd z ⟨by linarith [hz.1], hz.2⟩).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Ico] at hz
      exact (hd z ⟨by linarith [hz.1], hz.2⟩).hasDerivWithinAt
    · intro z hz
      rw [interior_Ico] at hz
      have : 0 < 1-z^2 := by nlinarith [hz.1, hz.2]
      positivity
  have hh := hm (show (0:ℝ) ∈ Ico 0 1 by constructor <;> norm_num) hy hy.1
  dsimp [f] at hh
  simp only [g, add_zero, sub_zero, Real.log_one, zero_div, zero_mul] at hh
  rw [← g_eq_artanh ⟨by linarith [hy.1], hy.2⟩]
  dsimp [g]
  linarith



/-- The manuscript's half-angle upper and lower rational functions. -/
noncomputable def U (c : ℝ) : ℝ := (19+11*c)/(3*(1+c)*(4+c))
noncomputable def V (c : ℝ) : ℝ := (11+19*c)/(3*(1+c)*(1+4*c))

lemma trig_domain {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi/2)) :
    Real.sin t ∈ Ioo 0 1 ∧ Real.cos t ∈ Ioo 0 1 := by
  have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  have he := Real.sin_sq_add_cos_sq t
  constructor <;> constructor <;> nlinarith [Real.sin_le_one t, Real.cos_le_one t]

lemma hasDerivAt_upper_gap {t : ℝ} (hc : 0 < Real.cos t) :
    HasDerivAt (fun t => Real.sin t * U (Real.cos t) - t)
      ((1-Real.cos t)^3 / ((1+Real.cos t)*(4+Real.cos t)^2)) t := by
  have hn : 3*(1+Real.cos t)*(4+Real.cos t) ≠ 0 := by positivity
  have hs : Real.sin t ^ 2 = 1-Real.cos t ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  convert ((Real.hasDerivAt_sin t).mul
    (((Real.hasDerivAt_cos t).const_mul 11 |>.const_add 19).div
      (((Real.hasDerivAt_cos t).const_add 1 |>.const_mul 3).mul
        ((Real.hasDerivAt_cos t).const_add 4)) hn)).sub (hasDerivAt_id t) using 1 <;> try rfl
  dsimp
  field_simp
  ring_nf
  rw [hs]
  ring

lemma hasDerivAt_lower_gap {t : ℝ} (ht : t ∈ Ioo (-(Real.pi/2)) (Real.pi/2)) :
    HasDerivAt (fun t => g (Real.sin t) - Real.sin t * V (Real.cos t))
      ((1-Real.cos t)^3 / (Real.cos t*(1+Real.cos t)*(1+4*Real.cos t)^2)) t := by
  have hc := Real.cos_pos_of_mem_Ioo ht
  have hs : Real.sin t ^ 2 = 1-Real.cos t ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hx : Real.sin t ∈ Ioo (-1) 1 := by
    constructor <;> nlinarith [sq_pos_of_pos hc, Real.sin_le_one t, Real.neg_one_le_sin t]
  have hn : 3*(1+Real.cos t)*(1+4*Real.cos t) ≠ 0 := by positivity
  have hg : HasDerivAt (fun t => g (Real.sin t)) (1 / Real.cos t) t := by
    convert (hasDerivAt_g hx).comp t (Real.hasDerivAt_sin t) using 1 <;> try rfl
    rw [hs]
    field_simp
    ring
  convert hg.sub ((Real.hasDerivAt_sin t).mul
    (((Real.hasDerivAt_cos t).const_mul 19 |>.const_add 11).div
      (((Real.hasDerivAt_cos t).const_add 1 |>.const_mul 3).mul
        ((Real.hasDerivAt_cos t).const_mul 4 |>.const_add 1)) hn)) using 1 <;> try rfl
  dsimp
  field_simp
  ring_nf
  rw [hs]
  ring

lemma angle_le_rational {t : ℝ} (ht : t ∈ Ico 0 (Real.pi/2)) :
    t ≤ Real.sin t * U (Real.cos t) := by
  have hd (z : ℝ) (hz : z ∈ Ico 0 (Real.pi/2)) :=
    hasDerivAt_upper_gap (Real.cos_pos_of_mem_Ioo ⟨by linarith [hz.1, Real.pi_pos], hz.2⟩)
  have hm : MonotoneOn (fun t => Real.sin t * U (Real.cos t) - t)
      (Ico 0 (Real.pi/2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico _ _)
    · intro z hz; exact (hd z hz).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Ico] at hz
      exact (hd z ⟨hz.1.le, hz.2⟩).hasDerivWithinAt
    · intro z hz
      rw [interior_Ico] at hz
      have hcz := (trig_domain hz).2
      have hc0 := hcz.1
      have : 0 ≤ 1-Real.cos z := by linarith [hcz.2]
      positivity
  have hh := hm ⟨le_rfl, by linarith [Real.pi_pos]⟩ ht ht.1
  simpa using hh

lemma odds_ge_rational {t : ℝ} (ht : t ∈ Ico 0 (Real.pi/2)) :
    Real.sin t * V (Real.cos t) ≤ g (Real.sin t) := by
  have hd (z : ℝ) (hz : z ∈ Ico 0 (Real.pi/2)) :=
    hasDerivAt_lower_gap ⟨by linarith [hz.1, Real.pi_pos], hz.2⟩
  have hm : MonotoneOn (fun t => g (Real.sin t) - Real.sin t * V (Real.cos t))
      (Ico 0 (Real.pi/2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico _ _)
    · intro z hz; exact (hd z hz).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Ico] at hz
      exact (hd z ⟨hz.1.le, hz.2⟩).hasDerivWithinAt
    · intro z hz
      rw [interior_Ico] at hz
      have hcz := (trig_domain hz).2
      have hc0 := hcz.1
      have : 0 ≤ 1-Real.cos z := by linarith [hcz.2]
      positivity
  have hh := hm ⟨le_rfl, by linarith [Real.pi_pos]⟩ ht ht.1
  simpa [g] using hh



lemma rational_curvature_identity {c : ℝ} (hc : 0 ≤ c) :
    16*(V c*(1+c^2)-(1-c^2)*(U c)^2-2)+25*(1-c^3*U c) =
      (1-c)*Q c/(9*(1+c)*(4+c)^2*(1+4*c)) := by
  unfold U V Q
  field_simp
  ring

lemma cubic_upper_lt_one {c : ℝ} (hc : c ∈ Ico 0 1) : c^3*U c < 1 := by
  have hd : 0 < 3*(1+c)*(4+c) := by have := hc.1; positivity
  have hp : 0 < (1-c)*(11*c^3+30*c^2+27*c+12) := by
    have := hc.1
    have : 0 < 1-c := sub_pos.mpr hc.2
    positivity
  unfold U
  rw [← mul_div_assoc, div_lt_one hd]
  nlinarith [hp]

/-- Curvature determinant in the manuscript's angular coordinate. -/
noncomputable def K (lam t : ℝ) : ℝ :=
  g (Real.sin t)*(1+Real.cos t^2)-Real.sin t*(t^2+2)+
    lam^2*(Real.sin t-Real.cos t^3*t)

lemma curvature_pos {lam t : ℝ} (hlam : 5/4 ≤ lam)
    (ht : t ∈ Ioo 0 (Real.pi/2)) : 0 < K lam t := by
  obtain ⟨hx, hc⟩ := trig_domain ht
  have hU : 0 < U (Real.cos t) := by unfold U; have := hc.1; positivity
  have htU := angle_le_rational ⟨ht.1.le, ht.2⟩
  have hgV := odds_ge_rational ⟨ht.1.le, ht.2⟩
  have htU2 : t^2 ≤ (Real.sin t * U (Real.cos t))^2 :=
    pow_le_pow_left₀ ht.1.le htU 2
  have hcoef : 0 < Real.sin t-Real.cos t^3*t := by
    have hcu := cubic_upper_lt_one ⟨hc.1.le, hc.2⟩
    have hh := mul_le_mul_of_nonneg_left htU (pow_nonneg hc.1.le 3)
    have hh' := mul_lt_mul_of_pos_left hcu hx.1
    nlinarith only [hh, hh']
  have hlam2 : (25:ℝ)/16 ≤ lam^2 := by nlinarith
  have hstep := mul_le_mul_of_nonneg_right hlam2 hcoef.le
  have hs : Real.sin t^2 = 1-Real.cos t^2 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hid := rational_curvature_identity hc.1.le
  have hcert : 0 < 16*(V (Real.cos t)*(1+Real.cos t^2)-
      (1-Real.cos t^2)*(U (Real.cos t))^2-2)+25*(1-Real.cos t^3*U (Real.cos t)) := by
    rw [hid]
    have := Q_pos ⟨hc.1.le, hc.2.le⟩
    have hc0 := hc.1
    have : 0 < 1-Real.cos t := sub_pos.mpr hc.2
    positivity
  have h1 := mul_le_mul_of_nonneg_right hgV (show 0 ≤ 1+Real.cos t^2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left htU2 hx.1.le
  have h3 := mul_le_mul_of_nonneg_left htU (show 0 ≤ 25*Real.cos t^3 by have := hc.1; positivity)
  have h4 := mul_pos hx.1 hcert
  rw [mul_pow, hs] at h2
  unfold K
  nlinarith only [hstep, h1, h2, h3, h4]



noncomputable def A (t : ℝ) : ℝ := Real.sin t*t
noncomputable def P (lam t : ℝ) : ℝ := phi (Real.sin t)+(t-lam*Real.sin t)^2/2
noncomputable def Ad (t : ℝ) : ℝ := Real.sin t+t*Real.cos t
noncomputable def Pd (lam t : ℝ) : ℝ :=
  g (Real.sin t)*Real.cos t+(t-lam*Real.sin t)*(1-lam*Real.cos t)
noncomputable def ratio (lam t : ℝ) : ℝ := Pd lam t/Ad t

lemma hasDerivAt_A (t : ℝ) : HasDerivAt A (Ad t) t := by
  convert (Real.hasDerivAt_sin t).mul (hasDerivAt_id t) using 1 <;> try rfl
  dsimp [Ad]
  ring

lemma hasDerivAt_Ad (t : ℝ) :
    HasDerivAt Ad (2*Real.cos t-t*Real.sin t) t := by
  convert (Real.hasDerivAt_sin t).add ((hasDerivAt_id t).mul (Real.hasDerivAt_cos t))
    using 1 <;> try rfl
  dsimp
  ring

lemma hasDerivAt_P (lam : ℝ) {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi/2)) :
    HasDerivAt (P lam) (Pd lam t) t := by
  have hx := (trig_domain ht).1
  convert ((hasDerivAt_phi ⟨by linarith [hx.1], hx.2⟩).comp t (Real.hasDerivAt_sin t)).add
    ((((hasDerivAt_id t).sub ((Real.hasDerivAt_sin t).const_mul lam)).pow 2).div_const 2)
    using 1 <;> try rfl
  dsimp [Pd]
  ring

lemma hasDerivAt_Pd (lam : ℝ) {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi/2)) :
    HasDerivAt (Pd lam)
      (1-g (Real.sin t)*Real.sin t+(1-lam*Real.cos t)^2+
        (t-lam*Real.sin t)*lam*Real.sin t) t := by
  obtain ⟨hx,hc⟩ := trig_domain ht
  have hs : Real.sin t^2 = 1-Real.cos t^2 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hg : HasDerivAt (fun t => g (Real.sin t)) (1/Real.cos t) t := by
    convert (hasDerivAt_g ⟨by linarith [hx.1], hx.2⟩).comp t (Real.hasDerivAt_sin t)
      using 1 <;> try rfl
    rw [hs]
    field_simp [ne_of_gt hc.1]
    ring
  convert (hg.mul (Real.hasDerivAt_cos t)).add
    (((hasDerivAt_id t).sub ((Real.hasDerivAt_sin t).const_mul lam)).mul
      (((Real.hasDerivAt_cos t).const_mul lam).const_sub 1)) using 1 <;> try rfl
  dsimp
  field_simp [ne_of_gt hc.1]
  ring

lemma Ad_pos {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi/2)) : 0 < Ad t := by
  obtain ⟨hx,hc⟩ := trig_domain ht
  unfold Ad
  exact add_pos hx.1 (mul_pos ht.1 hc.1)

lemma hasDerivAt_ratio (lam : ℝ) {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi/2)) :
    HasDerivAt (ratio lam) (-K lam t/(Ad t)^2) t := by
  have hn := ne_of_gt (Ad_pos ht)
  convert (hasDerivAt_Pd lam ht).div (hasDerivAt_Ad t) hn using 1 <;> try rfl
  apply congrArg (fun z : ℝ => z/(Ad t)^2)
  dsimp [K, Ad, Pd]
  have hs : Real.sin t^2 = 1-Real.cos t^2 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  ring_nf
  rw [hs]
  linear_combination lam^2*Real.sin t*(Real.sin_sq_add_cos_sq t)

lemma ratio_antitone {lam : ℝ} (hlam : 5/4 ≤ lam) :
    AntitoneOn (ratio lam) (Ioo 0 (Real.pi/2)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo _ _)
  · intro t ht
    exact (hasDerivAt_ratio lam ht).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ioo] at ht
    exact (hasDerivAt_ratio lam ht).hasDerivWithinAt
  · intro t ht
    rw [interior_Ioo] at ht
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (curvature_pos hlam ht).le)
      (sq_nonneg _)

/-- Supporting-line reduction from a tangent identity. The curvature inequality
is proved above, not assumed. -/
lemma supporting_line_reduction {lam alpha theta t : ℝ} (hlam : 5/4 ≤ lam)
    (ha : 0 < alpha) (hth : theta ∈ Ioo 0 (Real.pi/2))
    (ht : t ∈ Icc 0 (Real.pi/2)) (htangent : alpha*Pd lam theta = Ad theta) :
    alpha*(P lam t-P lam theta) ≤ A t-A theta := by
  let f : ℝ → ℝ := fun z => A z-alpha*P lam z
  have hf : Continuous f := by
    dsimp [f, A, P]
    exact (Real.continuous_sin.mul continuous_id).sub
      ((continuous_phi.comp Real.continuous_sin).add
        ((continuous_id.sub (continuous_const.mul Real.continuous_sin)).pow 2 |>.div_const 2)
        |>.const_mul alpha)
  have hd (z : ℝ) (hz : z ∈ Ioo 0 (Real.pi/2)) :
      HasDerivAt f (Ad z-alpha*Pd lam z) z :=
    (hasDerivAt_A z).sub ((hasDerivAt_P lam hz).const_mul alpha)
  have heq : alpha*ratio lam theta = 1 := by
    unfold ratio
    rw [← mul_div_assoc, htangent, div_self (ne_of_gt (Ad_pos hth))]
  have hm := ratio_antitone hlam
  have hmin : f theta ≤ f t := by
    rcases le_total t theta with hle | hge
    · have hm' : AntitoneOn f (Icc 0 theta) := by
        apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) hf.continuousOn
        · intro z hz
          rw [interior_Icc] at hz
          exact (hd z ⟨hz.1, lt_trans hz.2 hth.2⟩).hasDerivWithinAt
        · intro z hz
          rw [interior_Icc] at hz
          have hz' : z ∈ Ioo 0 (Real.pi/2) := ⟨hz.1, lt_trans hz.2 hth.2⟩
          have hr := mul_le_mul_of_nonneg_left (hm hz' hth hz.2.le) ha.le
          rw [heq] at hr
          change 1 ≤ alpha*(Pd lam z/Ad z) at hr
          rw [← mul_div_assoc, le_div_iff₀ (Ad_pos hz')] at hr
          linarith
      exact hm' ⟨ht.1, hle⟩ ⟨hth.1.le, le_rfl⟩ hle
    · have hm' : MonotoneOn f (Icc theta (Real.pi/2)) := by
        apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) hf.continuousOn
        · intro z hz
          rw [interior_Icc] at hz
          exact (hd z ⟨lt_trans hth.1 hz.1, hz.2⟩).hasDerivWithinAt
        · intro z hz
          rw [interior_Icc] at hz
          have hz' : z ∈ Ioo 0 (Real.pi/2) := ⟨lt_trans hth.1 hz.1, hz.2⟩
          have hr := mul_le_mul_of_nonneg_left (hm hth hz' hz.1.le) ha.le
          rw [heq] at hr
          change alpha*(Pd lam z/Ad z) ≤ 1 at hr
          rw [← mul_div_assoc, div_le_iff₀ (Ad_pos hz')] at hr
          linarith
      exact hm' ⟨le_rfl, hth.2.le⟩ ⟨hge, ht.2⟩ hge
  dsimp [f] at hmin
  linarith



/-- The slope of the entropy tangent at radius r. -/
noncomputable def alphaR (r : ℝ) : ℝ :=
  (Real.arcsin r+r/Real.sqrt (1-r^2))/g r

lemma alphaR_pos {r : ℝ} (hr : r ∈ Ioo 0 1) : 0 < alphaR r := by
  have hgr : 0 < g r := by
    rw [g_eq_artanh ⟨by linarith [hr.1], hr.2⟩]
    exact Real.artanh_pos hr
  have har := Real.arcsin_pos.mpr hr.1
  unfold alphaR
  exact div_pos (add_pos_of_pos_of_nonneg har (div_nonneg hr.1.le (Real.sqrt_nonneg _))) hgr

lemma tangent_identity {r : ℝ} (hr : r ∈ Ioo 0 1) :
    alphaR r * Pd (Real.arcsin r/r) (Real.arcsin r) = Ad (Real.arcsin r) := by
  have hgr : g r ≠ 0 := by
    rw [g_eq_artanh ⟨by linarith [hr.1], hr.2⟩]
    exact ne_of_gt (Real.artanh_pos hr)
  have hsr : Real.sqrt (1-r^2) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    nlinarith [hr.1, hr.2]
  unfold alphaR Pd Ad
  rw [Real.sin_arcsin (by linarith [hr.1]) hr.2.le, Real.cos_arcsin]
  field_simp [ne_of_gt hr.1, hgr, hsr]
  ring

/-- Centered support for every radius whose angular ratio is at least 5/4.
This theorem has no curvature or supporting-line hypotheses. -/
theorem centered_support_of_lambda {r x : ℝ} (hr : r ∈ Ioo 0 1)
    (hlam : 5/4 ≤ Real.arcsin r/r) (hx : x ∈ Icc (-1) 1) :
    (alphaR r/2)*(Real.arcsin x-(Real.arcsin r/r)*x)^2 ≤
      x*Real.arcsin x-r*Real.arcsin r-alphaR r*(phi x-phi r) := by
  have hpos (y : ℝ) (hy : y ∈ Icc 0 1) :
      (alphaR r/2)*(Real.arcsin y-(Real.arcsin r/r)*y)^2 ≤
        y*Real.arcsin y-r*Real.arcsin r-alphaR r*(phi y-phi r) := by
    have hth : Real.arcsin r ∈ Ioo 0 (Real.pi/2) :=
      ⟨Real.arcsin_pos.mpr hr.1, Real.arcsin_lt_pi_div_two.mpr hr.2⟩
    have ht : Real.arcsin y ∈ Icc 0 (Real.pi/2) :=
      ⟨Real.arcsin_nonneg.mpr hy.1, Real.arcsin_le_pi_div_two y⟩
    have hh := supporting_line_reduction hlam (alphaR_pos hr) hth ht (tangent_identity hr)
    unfold P A at hh
    rw [Real.sin_arcsin (by linarith [hy.1]) hy.2,
      Real.sin_arcsin (by linarith [hr.1]) hr.2.le,
      div_mul_cancel₀ _ (ne_of_gt hr.1), sub_self, zero_pow (by norm_num : 2 ≠ 0),
      zero_div, add_zero] at hh
    nlinarith only [hh]
  by_cases hxp : 0 ≤ x
  · exact hpos x ⟨hxp, hx.2⟩
  · have hh := hpos (-x) ⟨by linarith, by linarith [hx.1]⟩
    rw [Real.arcsin_neg, phi_even] at hh
    nlinarith only [hh]

/-- A fifth-order alternating upper bound, established by derivative comparison. -/
lemma sin_le_quintic {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x-x^3/6+x^5/120 := by
  have hc (z : ℝ) (hz : 0 ≤ z) : Real.cos z ≤ 1-z^2/2+z^4/24 := by
    let f : ℝ → ℝ := fun t => 1-t^2/2+t^4/24-Real.cos t
    have hd (t : ℝ) : deriv f t = -t+t^3/6+Real.sin t := by
      dsimp [f]
      simp (disch := fun_prop)
      ring
    have hm : MonotoneOn f (Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
      intro t ht
      rw [interior_Ici] at ht
      rw [hd]
      linarith [Real.sin_ge_sub_cube (le_of_lt ht)]
    have hh := hm (by simp : (0:ℝ) ∈ Ici 0) hz hz
    dsimp [f] at hh
    simp only [zero_pow (by norm_num : 2 ≠ 0), zero_pow (by norm_num : 4 ≠ 0),
      Real.cos_zero, zero_div] at hh
    linarith
  let f : ℝ → ℝ := fun t => t-t^3/6+t^5/120-Real.sin t
  have hd (t : ℝ) : deriv f t = 1-t^2/2+t^4/24-Real.cos t := by
    dsimp [f]
    simp (disch := fun_prop)
    ring
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [interior_Ici] at ht
    rw [hd]
    linarith [hc t (le_of_lt ht)]
  have hh := hm (by simp : (0:ℝ) ∈ Ici 0) hx hx
  simpa [f] using hh

lemma lambda_ge_of_sq {r : ℝ} (hr : r ∈ Ioo 0 1) (hr2 : 5/6 < r^2) :
    5/4 ≤ Real.arcsin r/r := by
  have hs := sin_le_quintic (show 0 ≤ 5*r/4 by linarith [hr.1])
  have hr4 : r^4 ≤ r^2 := by nlinarith [mul_nonneg (sq_nonneg r) (show 0 ≤ 1-r^2 by nlinarith [hr.1, hr.2])]
  have hpoly : 5/4-(125:ℝ)/384*r^2+3125/122880*r^4 < 1 := by nlinarith
  have hsin : Real.sin (5*r/4) < r := by
    have hh := mul_lt_mul_of_pos_right hpoly hr.1
    nlinarith only [hs, hh]
  have harg : 5*r/4 < Real.pi/2 := by
    have := Real.pi_gt_three
    linarith [hr.2]
  have hangle : 5*r/4 < Real.arcsin r := by
    apply Real.strictMonoOn_sin.lt_iff_lt
      ⟨by linarith [hr.1, Real.pi_pos], harg.le⟩ (Real.arcsin_mem_Icc r) |>.mp
    rwa [Real.sin_arcsin (by linarith [hr.1]) hr.2.le]
  rw [le_div_iff₀ hr.1]
  linarith



lemma exp_threshold : (22:ℝ) < Real.exp (31/10) := by
  have hh := Real.sum_le_exp_of_nonneg (by norm_num : 0 ≤ (31:ℝ)/10) 9
  norm_num [Finset.sum_range_succ] at hh
  linarith

lemma tanh_exp_two (ell : ℝ) :
    Real.tanh ell = (Real.exp (2*ell)-1)/(Real.exp (2*ell)+1) := by
  rw [Real.tanh_eq, Real.exp_neg, show 2*ell = ell+ell by ring, Real.exp_add]
  have hh := ne_of_gt (Real.exp_pos ell)
  field_simp

lemma tanh_sq_gt_threshold {ell : ℝ} (hell : 31/20 ≤ ell) :
    5/6 < (Real.tanh ell)^2 := by
  have he : 22 < Real.exp (2*ell) := lt_of_lt_of_le exp_threshold
    (Real.exp_le_exp.mpr (by linarith))
  have hr : 21/23 < Real.tanh ell := by
    rw [tanh_exp_two, lt_div_iff₀ (by positivity : 0 < Real.exp (2*ell)+1)]
    linarith
  nlinarith

lemma tanh_pos {ell : ℝ} (hell : 0 < ell) : 0 < Real.tanh ell := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hell) (Real.cosh_pos ell)

lemma alphaR_tanh (ell : ℝ) :
    alphaR (Real.tanh ell) = (Real.arcsin (Real.tanh ell)+Real.sinh ell)/ell := by
  have hr : Real.tanh ell ∈ Ioo (-1) 1 :=
    ⟨Real.neg_one_lt_tanh ell, Real.tanh_lt_one ell⟩
  unfold alphaR
  rw [g_eq_artanh hr, ← Real.sinh_artanh hr, Real.artanh_tanh]

/-- The exact centered-support inequality (mechanism.tex, centered-support.tex),
including the manuscript's threshold and all endpoints. -/
theorem centered_support {ell x : ℝ} (hell : 31/20 ≤ ell) (hx : x ∈ Icc (-1) 1) :
    let r := Real.tanh ell
    let theta := Real.arcsin r
    let lam := theta/r
    let alpha := (theta+Real.sinh ell)/ell
    (alpha/2)*(Real.arcsin x-lam*x)^2 ≤
      x*Real.arcsin x-r*theta-alpha*(phi x-phi r) := by
  have hep : 0 < ell := by linarith
  have hr : Real.tanh ell ∈ Ioo 0 1 := ⟨tanh_pos hep, Real.tanh_lt_one ell⟩
  have hh := centered_support_of_lambda hr
    (lambda_ge_of_sq hr (tanh_sq_gt_threshold hell)) hx
  rw [alphaR_tanh ell] at hh
  exact hh

end MostInformativeBit.CenteredSupport
