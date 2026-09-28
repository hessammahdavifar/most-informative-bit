import MostInformativeBit.ChannelBounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Scalar centered-edge inequalities of scalar.tex (S2)--(S4).

The convexity of the inverse profiles is used in the source only through
supporting lines. We prove those supporting lines directly in the height
parameter `v` (with `F v` the corresponding budget ratio), then derive the
inverse-profile form of (S2), convexity and monotonicity. -/
namespace MostInformativeBit.ScalarEdge
open Set Real ChannelProfiles

/-! ### Scalar profile facts -/

/-- `ell v = log (2 cosh v)`, written `\ell` in scalar.tex. -/
noncomputable def ell (v : ℝ) : ℝ := Real.log (2*Real.cosh v)

lemma two_cosh_eq (v : ℝ) : 2*Real.cosh v = Real.exp v*(1+Real.exp (-2*v)) := by
  rw [Real.cosh_eq, mul_add, mul_one, ← Real.exp_add, show v + -2*v = -v by ring]
  ring

lemma ell_eq (v : ℝ) : ell v = v + Real.log (1+Real.exp (-2*v)) := by
  unfold ell
  rw [two_cosh_eq, Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp]

lemma h_tanh (x : ℝ) : h (Real.tanh x) = ell x - x*Real.tanh x := by
  have hc := Real.cosh_pos x
  have ha : (1-Real.tanh x)/2 = Real.exp (-x)/(2*Real.cosh x) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
    field_simp
    ring
  have hb : 1-(1-Real.tanh x)/2 = Real.exp x/(2*Real.cosh x) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
    field_simp
    ring
  have hla : Real.log ((1-Real.tanh x)/2)⁻¹ = ell x + x := by
    rw [ha, inv_div, Real.log_div (by positivity) (Real.exp_pos _).ne', Real.log_exp]
    unfold ell
    ring
  have hlb : Real.log (1-(1-Real.tanh x)/2)⁻¹ = ell x - x := by
    rw [hb, inv_div, Real.log_div (by positivity) (Real.exp_pos _).ne', Real.log_exp]
    unfold ell
    ring
  unfold h Real.binEntropy
  rw [hla, hlb]
  ring

lemma h_neg (m : ℝ) : h (-m) = h m := by
  have := CenteredSupport.phi_even m
  unfold phi at this
  linarith

lemma h_nonneg {m : ℝ} (hm : m ∈ Icc (-1) 1) : 0 ≤ h m := by
  unfold h
  exact Real.binEntropy_nonneg (by linarith [hm.2]) (by linarith [hm.1])

lemma log_two_gt_half : (1:ℝ)/2 < Real.log 2 := by
  have := Real.log_two_gt_d9
  linarith

lemma ell_ge (v : ℝ) : Real.log 2 ≤ ell v :=
  Real.log_le_log (by norm_num) (by linarith [Real.one_le_cosh v])

lemma ell_pos (v : ℝ) : 0 < ell v :=
  lt_of_lt_of_le (Real.log_pos (by norm_num)) (ell_ge v)

lemma hasDerivAt_ell (v : ℝ) : HasDerivAt ell (Real.tanh v) v := by
  have h2 : (2*Real.cosh v) ≠ 0 := by positivity
  have hh : HasDerivAt ell _ v := ((Real.hasDerivAt_cosh v).const_mul 2).log h2
  refine hh.congr_deriv ?_
  rw [Real.tanh_eq_sinh_div_cosh]
  have := Real.cosh_pos v
  field_simp

lemma hasDerivAt_F' {v : ℝ} (hv : 0 < v) :
    HasDerivAt F (-(ell v)/(Real.sinh v)^2) v := by
  convert hasDerivAt_F hv using 2
  rw [h_tanh]
  ring

lemma sinh_pos' {v : ℝ} (hv : 0 < v) : 0 < Real.sinh v := Real.sinh_pos_iff.mpr hv

/-! ### Two generic comparison principles -/

/-- A function whose derivative is nonpositive left of `v` and nonnegative right
of `v` (on the positive half-line) is minimized at `v`. -/
lemma le_of_deriv_sign {G G' : ℝ → ℝ} {v : ℝ}
    (hG : ∀ k, 0 < k → HasDerivAt G (G' k) k)
    (hlt : ∀ k, 0 < k → k < v → G' k ≤ 0) (hgt : ∀ k, v < k → 0 ≤ G' k)
    {k : ℝ} (hv : 0 < v) (hk : 0 < k) : G v ≤ G k := by
  rcases le_total k v with hkv | hvk
  · have ha : AntitoneOn G (Icc k v) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc k v)
      · intro x hx
        exact (hG x (lt_of_lt_of_le hk hx.1)).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        exact (hG x (lt_trans hk hx.1)).hasDerivWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        exact hlt x (lt_trans hk hx.1) hx.2
    exact ha ⟨le_refl k, hkv⟩ ⟨hkv, le_refl v⟩ hkv
  · have hm : MonotoneOn G (Icc v k) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc v k)
      · intro x hx
        exact (hG x (lt_of_lt_of_le hv hx.1)).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        exact (hG x (lt_trans hv hx.1)).hasDerivWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        exact hgt x hx.1
    exact hm ⟨le_refl v, hvk⟩ ⟨hvk, le_refl k⟩ hvk

/-- An even differentiable function with nonnegative derivative on `(0,∞)` is
minimized at `0`. -/
lemma even_min {Φ Φ' : ℝ → ℝ} (hΦ : ∀ x, HasDerivAt Φ (Φ' x) x)
    (hpos : ∀ x, 0 < x → 0 ≤ Φ' x) (heven : ∀ x, Φ (-x) = Φ x) (x : ℝ) :
    Φ 0 ≤ Φ x := by
  have hm : MonotoneOn Φ (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · intro y _
      exact (hΦ y).continuousAt.continuousWithinAt
    · intro y _
      exact (hΦ y).hasDerivWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact hpos y hy
  rcases le_total 0 x with hx | hx
  · exact hm self_mem_Ici hx hx
  · rw [← heven x]
    exact hm self_mem_Ici (neg_nonneg.mpr hx) (neg_nonneg.mpr hx)

/-! ### Supporting-line slopes (scalar.tex, "Averaging by convexity") -/

/-- `-(F^{-1})'(F v) = sinh^2 v / ell v`. -/
noncomputable def slopeA (v : ℝ) : ℝ := (Real.sinh v)^2/ell v

/-- `-corr'(F v) = (sinh v - theta v)^2 / ell v`. -/
noncomputable def slopeC (v : ℝ) : ℝ := (Real.sinh v - theta v)^2/ell v

lemma slopeA_pos {v : ℝ} (hv : 0 < v) : 0 < slopeA v :=
  div_pos (pow_pos (sinh_pos' hv) 2) (ell_pos v)

lemma slopeC_nonneg (v : ℝ) : 0 ≤ slopeC v := div_nonneg (sq_nonneg _) (ell_pos v).le

lemma hasDerivAt_slopeA (k : ℝ) :
    HasDerivAt slopeA ((2*Real.sinh k*Real.cosh k*ell k -
      (Real.sinh k)^2*Real.tanh k)/(ell k)^2) k := by
  have hh : HasDerivAt slopeA _ k :=
    ((Real.hasDerivAt_sinh k).pow 2).div (hasDerivAt_ell k) (ell_pos k).ne'
  refine hh.congr_deriv ?_
  norm_num

/-- The source's claim that `sinh^2 k / ell k` increases, since `2 ell > tanh^2 k`. -/
lemma slopeA_strictMono : StrictMonoOn slopeA (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun k _ => (hasDerivAt_slopeA k).continuousAt.continuousWithinAt)
  intro k hk
  rw [interior_Ioi] at hk
  rw [(hasDerivAt_slopeA k).deriv]
  apply div_pos _ (pow_pos (ell_pos k) 2)
  have hs := sinh_pos' hk
  have hc := Real.cosh_pos k
  have ht1 := Real.tanh_lt_one k
  have ht0 := CenteredSupport.tanh_pos hk
  have he := ell_ge k
  have hl := log_two_gt_half
  have hid : 2*Real.sinh k*Real.cosh k*ell k - (Real.sinh k)^2*Real.tanh k =
      Real.sinh k*Real.cosh k*(2*ell k - (Real.tanh k)^2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
  rw [hid]
  apply mul_pos (mul_pos hs hc)
  nlinarith

lemma cosh_sub_inv_cosh (k : ℝ) :
    Real.cosh k - 1/Real.cosh k = Real.sinh k*Real.tanh k := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have := Real.cosh_pos k
  field_simp
  linear_combination Real.cosh_sq k

lemma hasDerivAt_slopeC (k : ℝ) :
    HasDerivAt slopeC ((Real.sinh k - theta k)*Real.tanh k*
      (2*Real.sinh k*ell k - (Real.sinh k - theta k))/(ell k)^2) k := by
  have hh : HasDerivAt slopeC _ k :=
    (((Real.hasDerivAt_sinh k).sub (hasDerivAt_theta k)).pow 2).div
    (hasDerivAt_ell k) (ell_pos k).ne'
  refine hh.congr_deriv ?_
  rw [cosh_sub_inv_cosh]
  norm_num
  ring

lemma theta_lt_sinh {k : ℝ} (hk : 0 < k) : theta k < Real.sinh k :=
  lt_trans (theta_lt_self hk) (self_lt_sinh hk)

/-- The source's claim that `(sinh k - theta k)^2 / ell k` increases,
since `2 ell sinh k > sinh k - theta k`. -/
lemma slopeC_strictMono : StrictMonoOn slopeC (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun k _ => (hasDerivAt_slopeC k).continuousAt.continuousWithinAt)
  intro k hk
  rw [interior_Ioi] at hk
  rw [(hasDerivAt_slopeC k).deriv]
  apply div_pos _ (pow_pos (ell_pos k) 2)
  have hs := sinh_pos' hk
  have hD := sub_pos.mpr (theta_lt_sinh hk)
  have ht0 := CenteredSupport.tanh_pos hk
  have htheta := theta_pos hk
  have he := ell_ge k
  have hl := log_two_gt_half
  apply mul_pos (mul_pos hD ht0)
  nlinarith

/-! ### Supporting lines in the height parameter -/

/-- Supporting line of the convex decreasing profile `F^{-1}` at `F v`, written in
heights: for `y = F k`, `F^{-1}(y) ≥ F^{-1}(F v) + (F^{-1})'(F v) (y - F v)`. -/
theorem height_tangent_action {v k : ℝ} (hv : 0 < v) (hk : 0 < k) :
    v - slopeA v*(F k - F v) ≤ k := by
  have hG : ∀ x, 0 < x → HasDerivAt (fun x => x + slopeA v*F x)
      (1 - slopeA v/slopeA x) x := by
    intro x hx
    have hh : HasDerivAt (fun x => x + slopeA v*F x) _ x :=
      (hasDerivAt_id x).add ((hasDerivAt_F' hx).const_mul (slopeA v))
    refine hh.congr_deriv ?_
    unfold slopeA
    have := ell_pos x
    have := sinh_pos' hx
    have := ell_pos v
    field_simp
    ring
  have key := le_of_deriv_sign (G := fun x => x + slopeA v*F x) hG ?_ ?_ hv hk
  · linarith
  · intro x hx hxv
    have hlt := slopeA_strictMono hx hv hxv
    have hp := slopeA_pos hx
    rw [sub_nonpos, le_div_iff₀ hp]
    linarith
  · intro x hvx
    have hx : 0 < x := lt_trans hv hvx
    have hlt := slopeA_strictMono hv hx hvx
    rw [sub_nonneg, div_le_one (slopeA_pos hx)]
    linarith

/-- Supporting line of the convex decreasing profile `corr` at `F v`, in heights. -/
theorem height_tangent_correction {v k : ℝ} (hv : 0 < v) (hk : 0 < k) :
    v - c v - slopeC v*(F k - F v) ≤ k - c k := by
  have hG : ∀ x, 0 < x → HasDerivAt (fun x => x - c x + slopeC v*F x)
      (ell x/(Real.sinh x)^2*(slopeC x - slopeC v)) x := by
    intro x hx
    have hh : HasDerivAt (fun x => x - c x + slopeC v*F x) _ x :=
      ((hasDerivAt_id x).sub (hasDerivAt_c hx)).add
      ((hasDerivAt_F' hx).const_mul (slopeC v))
    refine hh.congr_deriv ?_
    rw [show (1:ℝ) - cd x = (1 - s x)^2 from one_sub_cd x]
    unfold slopeC s
    have := ell_pos x
    have := sinh_pos' hx
    have := ell_pos v
    field_simp
    ring
  have key := le_of_deriv_sign (G := fun x => x - c x + slopeC v*F x) hG ?_ ?_ hv hk
  · linarith
  · intro x hx hxv
    have hlt := slopeC_strictMono hx hv hxv
    have hp : 0 < ell x/(Real.sinh x)^2 := div_pos (ell_pos x) (pow_pos (sinh_pos' hx) 2)
    exact mul_nonpos_of_nonneg_of_nonpos hp.le (by linarith)
  · intro x hvx
    have hx : 0 < x := lt_trans hv hvx
    have hlt := slopeC_strictMono hv hx hvx
    have hp : 0 < ell x/(Real.sinh x)^2 := div_pos (ell_pos x) (pow_pos (sinh_pos' hx) 2)
    exact mul_nonneg hp.le (by linarith)

/-! ### Centering property: (S3) and (S4) in the center parameter -/

lemma cosh_mul_cosh (v k : ℝ) :
    Real.cosh (v+k)*Real.cosh (v-k) = (Real.cosh v)^2 + (Real.sinh k)^2 := by
  rw [Real.cosh_add, Real.cosh_sub]
  linear_combination (Real.cosh v)^2*Real.cosh_sq k + (Real.sinh k)^2*Real.cosh_sq v

lemma tanh_sub_mul (v k : ℝ) :
    (Real.tanh (v+k) - Real.tanh (v-k))*(Real.cosh (v+k)*Real.cosh (v-k)) =
      2*Real.sinh k*Real.cosh k := by
  have hs := Real.sinh_sub (v+k) (v-k)
  rw [show v+k-(v-k) = 2*k by ring, Real.sinh_two_mul] at hs
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
  have := Real.cosh_pos (v+k)
  have := Real.cosh_pos (v-k)
  field_simp
  linear_combination -hs

/-- `sinh(2v) ell(v) ≥ v cosh(2v)` for `v ≥ 0`, the scalar core of the
source's chain `log[2(cosh x + C_k)] ≥ x coth x` (with `x = 2v`). -/
lemma sinh_two_mul_ell_ge {v : ℝ} (hv : 0 ≤ v) :
    v*Real.cosh (2*v) ≤ Real.sinh (2*v)*ell v := by
  rw [ell_eq, Real.sinh_eq, Real.cosh_eq, show -(2*v) = -2*v by ring]
  set t := Real.exp (-2*v) with ht
  set E := Real.exp (2*v) with hE
  have hEt : E*t = 1 := by rw [hE, ht, ← Real.exp_add]; simp
  have ht0 : 0 < t := Real.exp_pos _
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : 1 + 2*v ≤ E := by linarith [Real.add_one_le_exp (2*v)]
  have hL : t ≤ (1+t)*Real.log (1+t) := by
    have hh := Real.log_le_sub_one_of_pos (show 0 < 1/(1+t) by positivity)
    rw [one_div, Real.log_inv] at hh
    have h1 : (1+t)⁻¹ - 1 = -t/(1+t) := by field_simp; ring
    rw [h1, neg_div] at hh
    have h2 : t/(1+t) ≤ Real.log (1+t) := by linarith
    rwa [div_le_iff₀ (by positivity), mul_comm] at h2
  have hL' : 1 ≤ (E+1)*Real.log (1+t) := by nlinarith
  have hL0 : 0 ≤ Real.log (1+t) := Real.log_nonneg (by linarith)
  have hmain : 2*v ≤ (E^2-1)*Real.log (1+t) := by nlinarith
  nlinarith

/-- `P(v) (h(tanh(v+k)) + h(tanh(v-k)))`, written without the entropy. -/
noncomputable def centerPsi (k v : ℝ) : ℝ :=
  Real.cosh (v+k)*Real.cosh (v-k)*(ell (v+k) + ell (v-k)) -
    (v+k)*Real.sinh (v+k)*Real.cosh (v-k) - (v-k)*Real.sinh (v-k)*Real.cosh (v+k)

lemma centerPsi_eq (k v : ℝ) : centerPsi k v =
    Real.cosh (v+k)*Real.cosh (v-k)*(h (Real.tanh (v+k)) + h (Real.tanh (v-k))) := by
  rw [h_tanh, h_tanh, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
  unfold centerPsi
  have := Real.cosh_pos (v+k)
  have := Real.cosh_pos (v-k)
  field_simp
  ring

lemma hasDerivAt_centerPsi (k v : ℝ) : HasDerivAt (centerPsi k)
    (Real.sinh (2*v)*(ell (v+k) + ell (v-k)) - 2*v*Real.cosh (2*v)) v := by
  have ha : HasDerivAt (fun v : ℝ => v + k) 1 v := (hasDerivAt_id' v).add_const k
  have hb : HasDerivAt (fun v : ℝ => v - k) 1 v := (hasDerivAt_id' v).sub_const k
  have cA := (Real.hasDerivAt_cosh (v+k)).comp v ha
  have cB := (Real.hasDerivAt_cosh (v-k)).comp v hb
  have sA := (Real.hasDerivAt_sinh (v+k)).comp v ha
  have sB := (Real.hasDerivAt_sinh (v-k)).comp v hb
  have lA := (hasDerivAt_ell (v+k)).comp v ha
  have lB := (hasDerivAt_ell (v-k)).comp v hb
  have hall : HasDerivAt (centerPsi k) _ v :=
    (((cA.mul cB).mul (lA.add lB)).sub ((ha.mul sA).mul cB)).sub ((hb.mul sB).mul cA)
  refine hall.congr_deriv ?_
  simp only [Function.comp_apply, Pi.mul_apply, Pi.add_apply, mul_one, one_mul]
  have e1 : Real.sinh (2*v) = Real.sinh (v+k)*Real.cosh (v-k) + Real.cosh (v+k)*Real.sinh (v-k) := by
    rw [← Real.sinh_add]; ring_nf
  have e2 : Real.cosh (2*v) = Real.cosh (v+k)*Real.cosh (v-k) + Real.sinh (v+k)*Real.sinh (v-k) := by
    rw [← Real.cosh_add]; ring_nf
  rw [e1, e2, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
  have := Real.cosh_pos (v+k)
  have := Real.cosh_pos (v-k)
  field_simp
  ring

lemma ell_add_ell_ge (v k : ℝ) : 2*ell v ≤ ell (v+k) + ell (v-k) := by
  unfold ell
  rw [← Real.log_mul (by positivity) (by positivity), ← Real.log_rpow (by positivity)]
  apply Real.log_le_log (by positivity)
  rw [show (2*Real.cosh (v+k))*(2*Real.cosh (v-k)) =
    4*(Real.cosh (v+k)*Real.cosh (v-k)) by ring, cosh_mul_cosh]
  norm_num
  nlinarith [sq_nonneg (Real.sinh k)]

lemma centerPsi_deriv_nonneg (k : ℝ) {v : ℝ} (hv : 0 < v) :
    0 ≤ Real.sinh (2*v)*(ell (v+k) + ell (v-k)) - 2*v*Real.cosh (2*v) := by
  have hs : 0 ≤ Real.sinh (2*v) := (sinh_pos' (by linarith)).le
  have h1 := mul_le_mul_of_nonneg_left (ell_add_ell_ge v k) hs
  have h2 := sinh_two_mul_ell_ge hv.le
  nlinarith

lemma centerPsi_even (k v : ℝ) : centerPsi k (-v) = centerPsi k v := by
  rw [centerPsi_eq, centerPsi_eq, show -v+k = -(v-k) by ring, show -v-k = -(v+k) by ring,
    Real.cosh_neg, Real.cosh_neg, Real.tanh_neg, Real.tanh_neg, h_neg, h_neg]
  ring

/-- Centered entropy comparison (S3), in the center parameter:
`d F(k) ≤ H_e` for `p = tanh(v+k)`, `q = tanh(v-k)`. -/
theorem centered_entropy (v : ℝ) {k : ℝ} (hk : 0 < k) :
    (Real.tanh (v+k) - Real.tanh (v-k))/2*F k ≤
      (h (Real.tanh (v+k)) + h (Real.tanh (v-k)))/2 := by
  have hmin := even_min (hasDerivAt_centerPsi k) (fun x hx => centerPsi_deriv_nonneg k hx)
    (centerPsi_even k) v
  rw [centerPsi_eq, centerPsi_eq] at hmin
  simp only [zero_add, zero_sub, Real.cosh_neg, Real.tanh_neg, h_neg] at hmin
  have hP : 0 < Real.cosh (v+k)*Real.cosh (v-k) := by positivity
  have hd := tanh_sub_mul v k
  have hF : 2*Real.sinh k*Real.cosh k*F k = 2*(Real.cosh k)^2*h (Real.tanh k) := by
    unfold F
    rw [Real.tanh_eq_sinh_div_cosh]
    have := sinh_pos' hk
    have := Real.cosh_pos k
    field_simp
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right two_pos]
  apply le_of_mul_le_mul_right _ hP
  calc (Real.tanh (v+k) - Real.tanh (v-k))*F k*(Real.cosh (v+k)*Real.cosh (v-k))
      = 2*Real.sinh k*Real.cosh k*F k := by rw [← hd]; ring
    _ = 2*(Real.cosh k)^2*h (Real.tanh k) := hF
    _ ≤ _ := by nlinarith [hmin]

lemma theta_neg (x : ℝ) : theta (-x) = -theta x := by
  unfold theta
  rw [Real.tanh_neg, Real.arcsin_neg]

lemma theta_strictMono : StrictMono theta := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(hasDerivAt_theta x).deriv]
  exact one_div_pos.mpr (Real.cosh_pos x)

/-- `cosh v (theta(v+k) - theta(v-k)) ≤ 2 sinh k`: the half-angle identity
`theta(v+k)-theta(v-k) = 2 arctan(sinh k/cosh v)` with `arctan x ≤ x`,
proved by differentiating in `k`. -/
lemma cosh_mul_angle_le (v : ℝ) {k : ℝ} (hk : 0 ≤ k) :
    Real.cosh v*(theta (v+k) - theta (v-k)) ≤ 2*Real.sinh k := by
  have hd : ∀ k : ℝ, HasDerivAt (fun k => 2*Real.sinh k - Real.cosh v*(theta (v+k) - theta (v-k)))
      (2*Real.cosh k - Real.cosh v*(1/Real.cosh (v+k) + 1/Real.cosh (v-k))) k := by
    intro k
    have ha : HasDerivAt (fun k : ℝ => v + k) 1 k := (hasDerivAt_id' k).const_add v
    have hb : HasDerivAt (fun k : ℝ => v - k) (-1) k := by
      simpa using (hasDerivAt_id' k).const_sub v
    have hh := ((Real.hasDerivAt_sinh k).const_mul 2).sub
      ((((hasDerivAt_theta (v+k)).comp k ha).sub ((hasDerivAt_theta (v-k)).comp k hb)).const_mul
        (Real.cosh v))
    refine hh.congr_deriv ?_
    ring
  have hm : MonotoneOn (fun k => 2*Real.sinh k - Real.cosh v*(theta (v+k) - theta (v-k)))
      (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · intro y _
      exact (hd y).continuousAt.continuousWithinAt
    · intro y _
      exact (hd y).hasDerivWithinAt
    · intro y _
      have hsum : Real.cosh (v+y) + Real.cosh (v-y) = 2*Real.cosh v*Real.cosh y := by
        rw [Real.cosh_add, Real.cosh_sub]
        ring
      have hA := Real.cosh_pos (v+y)
      have hB := Real.cosh_pos (v-y)
      have hcv := Real.cosh_pos v
      have hcy := Real.cosh_pos y
      have he : Real.cosh v*(1/Real.cosh (v+y) + 1/Real.cosh (v-y)) =
          2*(Real.cosh v)^2*Real.cosh y/((Real.cosh v)^2 + (Real.sinh y)^2) := by
        rw [← cosh_mul_cosh]
        field_simp
        linear_combination hsum
      rw [he, sub_nonneg, div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg (Real.sinh y)]
  have hh := hm self_mem_Ici hk hk
  simp only [Real.sinh_zero, add_zero, sub_zero, sub_self, mul_zero] at hh
  linarith

noncomputable def centerW (k v : ℝ) : ℝ :=
  Real.cosh (v+k)*Real.cosh (v-k)*(theta (v+k) - theta (v-k))^2

lemma hasDerivAt_centerW (k v : ℝ) : HasDerivAt (centerW k)
    (2*Real.sinh v*(theta (v+k) - theta (v-k))*
      (Real.cosh v*(theta (v+k) - theta (v-k)) - 2*Real.sinh k)) v := by
  have ha : HasDerivAt (fun v : ℝ => v + k) 1 v := (hasDerivAt_id' v).add_const k
  have hb : HasDerivAt (fun v : ℝ => v - k) 1 v := (hasDerivAt_id' v).sub_const k
  have cA := (Real.hasDerivAt_cosh (v+k)).comp v ha
  have cB := (Real.hasDerivAt_cosh (v-k)).comp v hb
  have tA := (hasDerivAt_theta (v+k)).comp v ha
  have tB := (hasDerivAt_theta (v-k)).comp v hb
  have hall : HasDerivAt (centerW k) _ v := (cA.mul cB).mul ((tA.sub tB).pow 2)
  refine hall.congr_deriv ?_
  set D := theta (v+k) - theta (v-k)
  have h1 : Real.sinh (v+k)*Real.cosh (v-k) + Real.cosh (v+k)*Real.sinh (v-k) =
      2*Real.sinh v*Real.cosh v := by
    rw [← Real.sinh_add, show v+k+(v-k) = 2*v by ring, Real.sinh_two_mul]
  have h2 : Real.cosh (v+k)*Real.cosh (v-k)*(1/Real.cosh (v+k) - 1/Real.cosh (v-k)) =
      Real.cosh (v-k) - Real.cosh (v+k) := by
    have := Real.cosh_pos (v+k)
    have := Real.cosh_pos (v-k)
    field_simp
  have h3 : Real.cosh (v-k) - Real.cosh (v+k) = -2*Real.sinh v*Real.sinh k := by
    rw [Real.cosh_add, Real.cosh_sub]
    ring
  norm_num
  linear_combination D^2*h1 + 2*D*h2 + 2*D*h3

lemma centerW_even (k v : ℝ) : centerW k (-v) = centerW k v := by
  unfold centerW
  rw [show -v+k = -(v-k) by ring, show -v-k = -(v+k) by ring,
    Real.cosh_neg, Real.cosh_neg, theta_neg, theta_neg]
  ring

/-- Centered angle comparison (S4), in the center parameter:
`j ≤ d c(k)` for `p = tanh(v+k)`, `q = tanh(v-k)`. -/
theorem centered_angle (v : ℝ) {k : ℝ} (hk : 0 < k) :
    (theta (v+k) - theta (v-k))^2/4 ≤ (Real.tanh (v+k) - Real.tanh (v-k))/2*c k := by
  have hmin := even_min (Φ := fun v => -centerW k v) (fun x => (hasDerivAt_centerW k x).neg)
    (by
      intro x hx
      have hD : 0 ≤ theta (x+k) - theta (x-k) :=
        sub_nonneg.mpr (theta_strictMono.monotone (by linarith))
      have hB := cosh_mul_angle_le x hk.le
      have hs := sinh_pos' hx
      have : 2*Real.sinh x*(theta (x+k) - theta (x-k))*
          (Real.cosh x*(theta (x+k) - theta (x-k)) - 2*Real.sinh k) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
      linarith)
    (fun x => by simp only [centerW_even]) v
  simp only [neg_le_neg_iff] at hmin
  unfold centerW at hmin
  simp only [zero_add, zero_sub, Real.cosh_neg, theta_neg] at hmin
  have hP : 0 < Real.cosh (v+k)*Real.cosh (v-k) := by positivity
  have hd := tanh_sub_mul v k
  have hr : (Real.tanh (v+k) - Real.tanh (v-k))/2*c k =
      (Real.cosh k)^2*(theta k)^2/(Real.cosh (v+k)*Real.cosh (v-k)) := by
    rw [eq_div_iff hP.ne', show (Real.tanh (v+k) - Real.tanh (v-k))/2*c k*
      (Real.cosh (v+k)*Real.cosh (v-k)) =
      (Real.tanh (v+k) - Real.tanh (v-k))*(Real.cosh (v+k)*Real.cosh (v-k))*c k/2 by ring, hd]
    unfold c
    rw [Real.tanh_eq_sinh_div_cosh]
    have := sinh_pos' hk
    have := Real.cosh_pos k
    field_simp
  rw [hr, le_div_iff₀ hP]
  nlinarith [hmin]

/-! ### Edge quantities for `p, q ∈ (-1,1)` -/

/-- `d_edge = |p-q|/2`. -/
noncomputable def edgeWidth (p q : ℝ) : ℝ := |p-q|/2
/-- `H_e = (h p + h q)/2`. -/
noncomputable def edgeEntropy (p q : ℝ) : ℝ := (h p + h q)/2
/-- `a(p,q) = (p-q)(g p - g q)/4` with `g = artanh`. -/
noncomputable def edgeAction (p q : ℝ) : ℝ := (p-q)*(Real.artanh p - Real.artanh q)/4
/-- `j(p,q) = (arcsin p - arcsin q)^2/4`. -/
noncomputable def edgeAngle (p q : ℝ) : ℝ := (Real.arcsin p - Real.arcsin q)^2/4

lemma edgeWidth_comm (p q : ℝ) : edgeWidth p q = edgeWidth q p := by
  unfold edgeWidth; rw [abs_sub_comm]
lemma edgeEntropy_comm (p q : ℝ) : edgeEntropy p q = edgeEntropy q p := by
  unfold edgeEntropy; ring
lemma edgeAction_comm (p q : ℝ) : edgeAction p q = edgeAction q p := by
  unfold edgeAction; ring
lemma edgeAngle_comm (p q : ℝ) : edgeAngle p q = edgeAngle q p := by
  unfold edgeAngle; ring
lemma edgeWidth_nonneg (p q : ℝ) : 0 ≤ edgeWidth p q := by
  unfold edgeWidth; positivity
lemma edgeAngle_nonneg (p q : ℝ) : 0 ≤ edgeAngle p q := by
  unfold edgeAngle; positivity

lemma edgeEntropy_nonneg {p q : ℝ} (hp : p ∈ Ioo (-1) 1) (hq : q ∈ Ioo (-1) 1) :
    0 ≤ edgeEntropy p q := by
  unfold edgeEntropy
  have := h_nonneg (Ioo_subset_Icc_self hp)
  have := h_nonneg (Ioo_subset_Icc_self hq)
  positivity

/-- An oriented edge `q < p` written as `p = tanh(v+k)`, `q = tanh(v-k)` with
`k = (artanh p - artanh q)/2 > 0`: then `a = d k`, (S3) and (S4). -/
theorem edge_oriented {p q : ℝ} (hp : p ∈ Ioo (-1) 1) (hq : q ∈ Ioo (-1) 1) (hqp : q < p) :
    0 < (Real.artanh p - Real.artanh q)/2 ∧
    edgeAction p q = edgeWidth p q*((Real.artanh p - Real.artanh q)/2) ∧
    edgeWidth p q*F ((Real.artanh p - Real.artanh q)/2) ≤ edgeEntropy p q ∧
    edgeAngle p q ≤ edgeWidth p q*c ((Real.artanh p - Real.artanh q)/2) := by
  have hαβ : Real.artanh q < Real.artanh p := (Real.artanh_lt_artanh_iff hq hp).mpr hqp
  set α := Real.artanh p with hα
  set β := Real.artanh q with hβ
  have hk : 0 < (α-β)/2 := by linarith
  have hpα : Real.tanh α = p := Real.tanh_artanh hp
  have hqβ : Real.tanh β = q := Real.tanh_artanh hq
  have e1 : (α+β)/2 + (α-β)/2 = α := by ring
  have e2 : (α+β)/2 - (α-β)/2 = β := by ring
  have hw : edgeWidth p q = (p-q)/2 := by
    unfold edgeWidth; rw [abs_of_pos (sub_pos.mpr hqp)]
  refine ⟨hk, ?_, ?_, ?_⟩
  · rw [hw]; unfold edgeAction; ring
  · have hE := centered_entropy ((α+β)/2) hk
    rw [e1, e2, hpα, hqβ] at hE
    rw [hw]; exact hE
  · have hA := centered_angle ((α+β)/2) hk
    rw [e1, e2] at hA
    simp only [theta, hpα, hqβ] at hA
    rw [hw]; exact hA

/-- The edge action in the form `a = d k`, `k = |artanh p - artanh q|/2`. -/
theorem edgeAction_eq {p q : ℝ} (hp : p ∈ Ioo (-1) 1) (hq : q ∈ Ioo (-1) 1) :
    edgeAction p q = edgeWidth p q*(|Real.artanh p - Real.artanh q|/2) := by
  rcases lt_trichotomy q p with hqp | rfl | hpq
  · rw [(edge_oriented hp hq hqp).2.1, abs_of_pos (by linarith [(edge_oriented hp hq hqp).1])]
  · simp [edgeAction, edgeWidth]
  · rw [edgeAction_comm, edgeWidth_comm, (edge_oriented hq hp hpq).2.1, abs_sub_comm,
      abs_of_pos (by linarith [(edge_oriented hq hp hpq).1])]

/-- (S3): for `p ≠ q`, `H_e ≥ d_edge F(k)` with `k = |artanh p - artanh q|/2 > 0`. -/
theorem edge_S3 {p q : ℝ} (hp : p ∈ Ioo (-1) 1) (hq : q ∈ Ioo (-1) 1) :
    edgeWidth p q*F (|Real.artanh p - Real.artanh q|/2) ≤ edgeEntropy p q := by
  rcases lt_trichotomy q p with hqp | rfl | hpq
  · rw [abs_of_pos (by linarith [(edge_oriented hp hq hqp).1])]
    exact (edge_oriented hp hq hqp).2.2.1
  · simp only [edgeWidth, sub_self, abs_zero, zero_div, zero_mul]
    exact edgeEntropy_nonneg hp hp
  · rw [edgeEntropy_comm, edgeWidth_comm, abs_sub_comm,
      abs_of_pos (by linarith [(edge_oriented hq hp hpq).1])]
    exact (edge_oriented hq hp hpq).2.2.1

/-- (S4): `j ≤ d_edge c(k)` with `k = |artanh p - artanh q|/2`. -/
theorem edge_S4 {p q : ℝ} (hp : p ∈ Ioo (-1) 1) (hq : q ∈ Ioo (-1) 1) :
    edgeAngle p q ≤ edgeWidth p q*c (|Real.artanh p - Real.artanh q|/2) := by
  rcases lt_trichotomy q p with hqp | rfl | hpq
  · rw [abs_of_pos (by linarith [(edge_oriented hp hq hqp).1])]
    exact (edge_oriented hp hq hqp).2.2.2
  · simp [edgeAngle, edgeWidth]
  · rw [edgeAngle_comm, edgeWidth_comm, abs_sub_comm,
      abs_of_pos (by linarith [(edge_oriented hq hp hpq).1])]
    exact (edge_oriented hq hp hpq).2.2.2

/-- `a - j ≥ d_edge (k - c k) ≥ 0`. -/
theorem edgeAngle_le_edgeAction {p q : ℝ} (hp : p ∈ Ioo (-1) 1) (hq : q ∈ Ioo (-1) 1) :
    edgeAngle p q ≤ edgeAction p q := by
  have h4 := edge_S4 hp hq
  rw [edgeAction_eq hp hq]
  have hc := c_le_self (show 0 ≤ |Real.artanh p - Real.artanh q|/2 by positivity)
  have hd := edgeWidth_nonneg p q
  nlinarith [mul_le_mul_of_nonneg_left hc hd]

theorem edgeAction_nonneg {p q : ℝ} (hp : p ∈ Ioo (-1) 1) (hq : q ∈ Ioo (-1) 1) :
    0 ≤ edgeAction p q :=
  le_trans (edgeAngle_nonneg p q) (edgeAngle_le_edgeAction hp hq)

/-! ### (S2) as supporting-line inequalities at an arbitrary height `v > 0`

These are the pointwise inequalities that Jensen's inequality is applied to.
Zero-width edges (`p = q`) are included: there both sides reduce to
`-slope * h p ≤ 0`. -/

theorem edge_action_tangent {p q : ℝ} (hp : p ∈ Ioo (-1) 1) (hq : q ∈ Ioo (-1) 1)
    {v : ℝ} (hv : 0 < v) :
    edgeWidth p q*v - slopeA v*(edgeEntropy p q - F v*edgeWidth p q) ≤ edgeAction p q := by
  have hs := slopeA_pos hv
  have key : ∀ {p q : ℝ}, p ∈ Ioo (-1) 1 → q ∈ Ioo (-1) 1 → q < p →
      edgeWidth p q*v - slopeA v*(edgeEntropy p q - F v*edgeWidth p q) ≤ edgeAction p q := by
    intro p q hp hq hqp
    obtain ⟨hk, ha, hH, -⟩ := edge_oriented hp hq hqp
    have ht := height_tangent_action hv hk
    have hd := edgeWidth_nonneg p q
    rw [ha]
    nlinarith [mul_le_mul_of_nonneg_left ht hd, mul_le_mul_of_nonneg_left hH hs.le]
  rcases lt_trichotomy q p with hqp | rfl | hpq
  · exact key hp hq hqp
  · have := edgeEntropy_nonneg hp hp
    simp only [edgeWidth, edgeAction, sub_self, abs_zero, zero_div, zero_mul, mul_zero,
      sub_zero, zero_sub]
    nlinarith
  · have := key hq hp hpq
    rwa [edgeWidth_comm, edgeEntropy_comm, edgeAction_comm]

theorem edge_correction_tangent {p q : ℝ} (hp : p ∈ Ioo (-1) 1) (hq : q ∈ Ioo (-1) 1)
    {v : ℝ} (hv : 0 < v) :
    edgeWidth p q*(v - c v) - slopeC v*(edgeEntropy p q - F v*edgeWidth p q) ≤
      edgeAction p q - edgeAngle p q := by
  have hs := slopeC_nonneg v
  have key : ∀ {p q : ℝ}, p ∈ Ioo (-1) 1 → q ∈ Ioo (-1) 1 → q < p →
      edgeWidth p q*(v - c v) - slopeC v*(edgeEntropy p q - F v*edgeWidth p q) ≤
        edgeAction p q - edgeAngle p q := by
    intro p q hp hq hqp
    obtain ⟨hk, ha, hH, hj⟩ := edge_oriented hp hq hqp
    have ht := height_tangent_correction hv hk
    have hd := edgeWidth_nonneg p q
    rw [ha]
    nlinarith [mul_le_mul_of_nonneg_left ht hd, mul_le_mul_of_nonneg_left hH hs]
  rcases lt_trichotomy q p with hqp | rfl | hpq
  · exact key hp hq hqp
  · have := edgeEntropy_nonneg hp hp
    simp only [edgeWidth, edgeAction, edgeAngle, sub_self, abs_zero, zero_div, zero_mul,
      mul_zero, sub_zero, zero_sub, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow]
    nlinarith
  · have := key hq hp hpq
    rwa [edgeWidth_comm, edgeEntropy_comm, edgeAction_comm, edgeAngle_comm]

/-! ### Inverse profiles `F⁻¹`, `corr` and the literal form of (S2) -/

lemma h_pos {m : ℝ} (hm : m ∈ Ioo (-1) 1) : 0 < h m := by
  unfold h
  apply Real.binEntropy_pos <;> linarith [hm.1, hm.2]

/-- The unique positive height with `F v = y` (the source's `F⁻¹ y`) for `y > 0`;
the value `0` for `y ≤ 0` is never used. -/
noncomputable def Finv (y : ℝ) : ℝ :=
  if hy : 0 < y then (ChannelBounds.existsUnique_height hy).exists.choose else 0

lemma Finv_spec {y : ℝ} (hy : 0 < y) : 0 < Finv y ∧ F (Finv y) = y := by
  unfold Finv
  rw [dif_pos hy]
  exact (ChannelBounds.existsUnique_height hy).exists.choose_spec

lemma Finv_F {v : ℝ} (hv : 0 < v) : Finv (F v) = v :=
  F_strictAnti.injOn (Finv_spec (F_pos hv)).1 hv (Finv_spec (F_pos hv)).2

/-- `corr = (id - c) ∘ F⁻¹`, i.e. `corr(F k) = k - theta(k)^2/tanh k`. -/
noncomputable def corrFn (y : ℝ) : ℝ := Finv y - c (Finv y)

lemma corrFn_F {v : ℝ} (hv : 0 < v) : corrFn (F v) = v - c v := by
  unfold corrFn; rw [Finv_F hv]

/-- Supporting line of `F⁻¹` at every `y0 > 0`, slope `-(sinh² k / ell k)`, `k = F⁻¹ y0`. -/
theorem Finv_tangent {y0 y : ℝ} (hy0 : 0 < y0) (hy : 0 < y) :
    Finv y0 - slopeA (Finv y0)*(y - y0) ≤ Finv y := by
  obtain ⟨h1, h2⟩ := Finv_spec hy0
  obtain ⟨h3, h4⟩ := Finv_spec hy
  have hh := height_tangent_action h1 h3
  rwa [h2, h4] at hh

/-- Supporting line of `corr` at every `y0 > 0`, slope `-((sinh k - theta k)² / ell k)`. -/
theorem corrFn_tangent {y0 y : ℝ} (hy0 : 0 < y0) (hy : 0 < y) :
    corrFn y0 - slopeC (Finv y0)*(y - y0) ≤ corrFn y := by
  obtain ⟨h1, h2⟩ := Finv_spec hy0
  obtain ⟨h3, h4⟩ := Finv_spec hy
  have hh := height_tangent_correction h1 h3
  rw [h2, h4] at hh
  unfold corrFn
  linarith

lemma convexOn_of_tangent {D : Set ℝ} (hD : Convex ℝ D) {f m : ℝ → ℝ}
    (ht : ∀ x ∈ D, ∀ y ∈ D, f x + m x*(y - x) ≤ f y) : ConvexOn ℝ D f := by
  refine ⟨hD, fun x hx y hy a b ha hb hab => ?_⟩
  have hz := hD hx hy ha hb hab
  have h1 := ht _ hz x hx
  have h2 := ht _ hz y hy
  simp only [smul_eq_mul] at *
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

theorem Finv_convexOn : ConvexOn ℝ (Ioi 0) Finv :=
  convexOn_of_tangent (convex_Ioi 0) (m := fun y0 => -slopeA (Finv y0))
    (fun x hx y hy => by have := Finv_tangent hx hy; linarith)

theorem corrFn_convexOn : ConvexOn ℝ (Ioi 0) corrFn :=
  convexOn_of_tangent (convex_Ioi 0) (m := fun y0 => -slopeC (Finv y0))
    (fun x hx y hy => by have := corrFn_tangent hx hy; linarith)

theorem Finv_antitoneOn : AntitoneOn Finv (Ioi 0) := by
  intro y0 hy0 y hy hle
  have ht := Finv_tangent (show (0:ℝ) < y from hy) (show (0:ℝ) < y0 from hy0)
  have hs := slopeA_pos (Finv_spec (show (0:ℝ) < y from hy)).1
  nlinarith

theorem corrFn_antitoneOn : AntitoneOn corrFn (Ioi 0) := by
  intro y0 hy0 y hy hle
  have ht := corrFn_tangent (show (0:ℝ) < y from hy) (show (0:ℝ) < y0 from hy0)
  have hs := slopeC_nonneg (Finv y)
  nlinarith

lemma c_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ c v := by
  rcases eq_or_lt_of_le hv with rfl | hv
  · rw [c_zero]
  · exact div_nonneg (sq_nonneg _) (CenteredSupport.tanh_pos hv).le

lemma corrFn_nonneg {y : ℝ} (hy : 0 < y) : 0 ≤ corrFn y := by
  unfold corrFn
  linarith [c_le_self (Finv_spec hy).1.le]

lemma corrFn_le_Finv {y : ℝ} (hy : 0 < y) : corrFn y ≤ Finv y := by
  unfold corrFn
  linarith [c_nonneg (Finv_spec hy).1.le]

/-- The perspective `d ψ(H/d)` of a function with supporting lines on `(0,∞)` is
jointly convex on `d > 0`, `H > 0`. -/
theorem perspective_convexOn {ψ m : ℝ → ℝ}
    (ht : ∀ y0, 0 < y0 → ∀ y, 0 < y → ψ y0 + m y0*(y - y0) ≤ ψ y) :
    ConvexOn ℝ (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) (fun w : ℝ × ℝ => w.1*ψ (w.2/w.1)) := by
  have hD : Convex ℝ (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) := (convex_Ioi 0).prod (convex_Ioi 0)
  refine ⟨hD, fun x hx y hy a b ha hb hab => ?_⟩
  have hz := hD hx hy ha hb hab
  set z := a • x + b • y with hzdef
  have hz1 : z.1 = a*x.1 + b*y.1 := by simp [hzdef]
  have hz2 : z.2 = a*x.2 + b*y.2 := by simp [hzdef]
  have hzp : 0 < z.1 := hz.1
  have hy0 : 0 < z.2/z.1 := div_pos hz.2 hz.1
  -- the supporting linear functional at `z`
  have hsupp : ∀ w : ℝ × ℝ, 0 < w.1 → 0 < w.2 →
      (ψ (z.2/z.1) - m (z.2/z.1)*(z.2/z.1))*w.1 + m (z.2/z.1)*w.2 ≤ w.1*ψ (w.2/w.1) := by
    intro w hw1 hw2
    have hh := mul_le_mul_of_nonneg_left (ht _ hy0 _ (div_pos hw2 hw1)) hw1.le
    have he : w.1*(ψ (z.2/z.1) + m (z.2/z.1)*(w.2/w.1 - z.2/z.1)) =
        (ψ (z.2/z.1) - m (z.2/z.1)*(z.2/z.1))*w.1 + m (z.2/z.1)*w.2 := by
      field_simp
      ring
    linarith
  have hbase : z.1*ψ (z.2/z.1) =
      (ψ (z.2/z.1) - m (z.2/z.1)*(z.2/z.1))*z.1 + m (z.2/z.1)*z.2 := by
    field_simp
    ring
  have h1 := hsupp x hx.1 hx.2
  have h2 := hsupp y hy.1 hy.2
  simp only [smul_eq_mul]
  rw [hbase]
  set A := ψ (z.2/z.1) - m (z.2/z.1)*(z.2/z.1)
  set B := m (z.2/z.1)
  rw [hz1, hz2]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

theorem Finv_perspective_convexOn :
    ConvexOn ℝ (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) (fun w : ℝ × ℝ => w.1*Finv (w.2/w.1)) :=
  perspective_convexOn (m := fun y0 => -slopeA (Finv y0))
    (fun y0 hy0 y hy => by have := Finv_tangent hy0 hy; linarith)

theorem corrFn_perspective_convexOn :
    ConvexOn ℝ (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) (fun w : ℝ × ℝ => w.1*corrFn (w.2/w.1)) :=
  perspective_convexOn (m := fun y0 => -slopeC (Finv y0))
    (fun y0 hy0 y hy => by have := corrFn_tangent hy0 hy; linarith)

/-- The perspectives decrease in `H` (for fixed `d > 0`). -/
theorem Finv_perspective_antitone {d H H' : ℝ} (hd : 0 < d) (hH : 0 < H) (hHH : H ≤ H') :
    d*Finv (H'/d) ≤ d*Finv (H/d) :=
  mul_le_mul_of_nonneg_left (Finv_antitoneOn (show 0 < H/d from div_pos hH hd)
    (show 0 < H'/d from div_pos (by linarith) hd) (div_le_div_of_nonneg_right hHH hd.le)) hd.le

theorem corrFn_perspective_antitone {d H H' : ℝ} (hd : 0 < d) (hH : 0 < H) (hHH : H ≤ H') :
    d*corrFn (H'/d) ≤ d*corrFn (H/d) :=
  mul_le_mul_of_nonneg_left (corrFn_antitoneOn (show 0 < H/d from div_pos hH hd)
    (show 0 < H'/d from div_pos (by linarith) hd) (div_le_div_of_nonneg_right hHH hd.le)) hd.le

open Filter Topology in
lemma tendsto_Finv_atTop : Tendsto Finv atTop (𝓝 0) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [eventually_gt_atTop 0] with y hy
    exact lt_trans ha (Finv_spec hy).1
  · intro a ha
    have ha2 : 0 < a/2 := by linarith
    filter_upwards [eventually_gt_atTop (F (a/2))] with y hy
    have hy0 : 0 < y := lt_trans (F_pos ha2) hy
    have hh := Finv_antitoneOn (show 0 < F (a/2) from F_pos ha2) (show 0 < y from hy0) hy.le
    rw [Finv_F ha2] at hh
    linarith

open Filter Topology in
/-- Zero-width limit: `d F⁻¹(H/d) → 0` as `d ↓ 0`. -/
theorem Finv_perspective_tendsto_zero {H : ℝ} (hH : 0 < H) :
    Tendsto (fun d => d*Finv (H/d)) (𝓝[>] 0) (𝓝 0) := by
  have hy : Tendsto (fun d : ℝ => H/d) (𝓝[>] 0) atTop := by
    simpa only [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop hH
  have hd : Tendsto (fun d : ℝ => d) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  simpa using hd.mul (tendsto_Finv_atTop.comp hy)

open Filter Topology in
/-- Zero-width limit: `d corr(H/d) → 0` as `d ↓ 0`. -/
theorem corrFn_perspective_tendsto_zero {H : ℝ} (hH : 0 < H) :
    Tendsto (fun d => d*corrFn (H/d)) (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (Finv_perspective_tendsto_zero hH)
  · filter_upwards [self_mem_nhdsWithin] with d hd
    exact mul_nonneg (le_of_lt hd) (corrFn_nonneg (div_pos hH hd))
  · filter_upwards [self_mem_nhdsWithin] with d hd
    exact mul_le_mul_of_nonneg_left (corrFn_le_Finv (div_pos hH hd)) (le_of_lt hd)

lemma edgeWidth_pos {p q : ℝ} (hpq : p ≠ q) : 0 < edgeWidth p q := by
  unfold edgeWidth
  have := abs_pos.mpr (sub_ne_zero.mpr hpq)
  positivity

lemma edgeEntropy_pos {p q : ℝ} (hp : p ∈ Ioo (-1) 1) (hq : q ∈ Ioo (-1) 1) :
    0 < edgeEntropy p q := by
  unfold edgeEntropy
  have := h_pos hp
  have := h_pos hq
  positivity

/-- (S2), first inequality: `a(p,q) ≥ d_edge F⁻¹(H_e/d_edge)` for `p ≠ q`. -/
theorem S2_action {p q : ℝ} (hp : p ∈ Ioo (-1) 1) (hq : q ∈ Ioo (-1) 1) (hpq : p ≠ q) :
    edgeWidth p q*Finv (edgeEntropy p q/edgeWidth p q) ≤ edgeAction p q := by
  have hd := edgeWidth_pos hpq
  have hy := div_pos (edgeEntropy_pos hp hq) hd
  obtain ⟨hv, hFv⟩ := Finv_spec hy
  have ht := edge_action_tangent hp hq hv
  rw [hFv, div_mul_cancel₀ _ hd.ne', sub_self, mul_zero, sub_zero] at ht
  exact ht

/-- (S2), second inequality: `a(p,q) - j(p,q) ≥ d_edge corr(H_e/d_edge)` for `p ≠ q`. -/
theorem S2_correction {p q : ℝ} (hp : p ∈ Ioo (-1) 1) (hq : q ∈ Ioo (-1) 1) (hpq : p ≠ q) :
    edgeWidth p q*corrFn (edgeEntropy p q/edgeWidth p q) ≤ edgeAction p q - edgeAngle p q := by
  have hd := edgeWidth_pos hpq
  have hy := div_pos (edgeEntropy_pos hp hq) hd
  obtain ⟨hv, hFv⟩ := Finv_spec hy
  have ht := edge_correction_tangent hp hq hv
  rw [hFv, div_mul_cancel₀ _ hd.ne', sub_self, mul_zero, sub_zero] at ht
  exact ht

end MostInformativeBit.ScalarEdge
