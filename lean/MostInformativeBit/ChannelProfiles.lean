import MostInformativeBit.CenteredSupport
import Mathlib.Analysis.Convex.Deriv

/-! Channel profiles of mechanism.tex and profile-rates.tex. -/
namespace MostInformativeBit.ChannelProfiles
open Set Real

noncomputable def theta (v : ℝ) : ℝ := Real.arcsin (Real.tanh v)
noncomputable def F (v : ℝ) : ℝ := h (Real.tanh v)/Real.tanh v
noncomputable def c (v : ℝ) : ℝ := (theta v)^2/Real.tanh v
noncomputable def s (v : ℝ) : ℝ := theta v/Real.sinh v
noncomputable def cd (v : ℝ) : ℝ := 2*s v-(s v)^2
noncomputable def sd (v : ℝ) : ℝ :=
  ((1/Real.cosh v)^2-s v)/Real.tanh v

lemma hasDerivAt_tanh (v : ℝ) : HasDerivAt Real.tanh (1/(Real.cosh v)^2) v := by
  have hc := ne_of_gt (Real.cosh_pos v)
  convert (Real.hasDerivAt_sinh v).div (Real.hasDerivAt_cosh v) hc using 1 <;> try rfl
  · exact funext fun x => Real.tanh_eq_sinh_div_cosh x
  · apply congrArg (fun z : ℝ => z/(Real.cosh v)^2)
    nlinarith [Real.cosh_sq_sub_sinh_sq v]

lemma continuous_tanh : Continuous Real.tanh :=
  continuous_iff_continuousAt.mpr fun v => (hasDerivAt_tanh v).continuousAt

lemma cosh_eq_inv_sqrt (v : ℝ) :
    Real.cosh v = 1/Real.sqrt (1-(Real.tanh v)^2) := by
  simpa only [Real.artanh_tanh] using
    Real.cosh_artanh ⟨Real.neg_one_lt_tanh v, Real.tanh_lt_one v⟩

lemma hasDerivAt_theta (v : ℝ) : HasDerivAt theta (1/Real.cosh v) v := by
  have ht1 := ne_of_lt (Real.tanh_lt_one v)
  have htm := ne_of_gt (Real.neg_one_lt_tanh v)
  convert (Real.hasDerivAt_arcsin htm ht1).comp v (hasDerivAt_tanh v) using 1 <;> try rfl
  rw [← cosh_eq_inv_sqrt v]
  field_simp

lemma continuous_theta : Continuous theta :=
  continuous_iff_continuousAt.mpr fun v => (hasDerivAt_theta v).continuousAt

lemma theta_pos {v : ℝ} (hv : 0 < v) : 0 < theta v :=
  Real.arcsin_pos.mpr (CenteredSupport.tanh_pos hv)

lemma theta_lt_self {v : ℝ} (hv : 0 < v) : theta v < v := by
  have hd (v : ℝ) : HasDerivAt (fun v => v-theta v) (1-1/Real.cosh v) v :=
    (hasDerivAt_id v).sub (hasDerivAt_theta v)
  have hm : StrictMonoOn (fun v => v-theta v) (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
      (continuous_id.sub continuous_theta).continuousOn
    intro v hv
    rw [interior_Ici] at hv
    change 0 < deriv (fun v => v-theta v) v
    rw [(hd v).deriv]
    have hc := Real.one_lt_cosh.mpr (ne_of_gt hv)
    have hh : 1/Real.cosh v < 1 := (div_lt_one (Real.cosh_pos v)).mpr hc
    linarith
  have hh := hm (by simp : (0:ℝ) ∈ Ici 0) hv.le hv
  simpa [theta] using hh

lemma self_lt_sinh {v : ℝ} (hv : 0 < v) : v < Real.sinh v := by
  have hh := Real.sinh_sub_id_strictMono hv
  simpa using hh

lemma s_pos {v : ℝ} (hv : 0 < v) : 0 < s v :=
  div_pos (theta_pos hv) (Real.sinh_pos_iff.mpr hv)

lemma s_lt_one {v : ℝ} (hv : 0 < v) : s v < 1 := by
  apply (div_lt_one (Real.sinh_pos_iff.mpr hv)).mpr
  exact lt_trans (theta_lt_self hv) (self_lt_sinh hv)

lemma tanh_lt_theta {v : ℝ} (hv : 0 < v) : Real.tanh v < theta v := by
  have hh := Real.sin_lt (theta_pos hv)
  rwa [theta, Real.sin_arcsin (Real.neg_one_lt_tanh v).le (Real.tanh_lt_one v).le] at hh

lemma sd_neg {v : ℝ} (hv : 0 < v) : sd v < 0 := by
  have hs := Real.sinh_pos_iff.mpr hv
  have hc := Real.cosh_pos v
  have hc1 := Real.one_lt_cosh.mpr (ne_of_gt hv)
  have ht := tanh_lt_theta hv
  rw [Real.tanh_eq_sinh_div_cosh] at ht
  have ht' := (div_lt_iff₀ hc).mp ht
  have htt := mul_lt_mul_of_pos_right ht' hc
  have htheta := theta_pos hv
  have hp : (1/Real.cosh v)^2 < s v := by
    unfold s
    apply (lt_div_iff₀ hs).mpr
    rw [div_pow, one_pow, one_div_mul_eq_div]
    apply (div_lt_iff₀ (sq_pos_of_pos hc)).mpr
    nlinarith
  unfold sd
  exact div_neg_of_neg_of_pos (sub_neg.mpr hp) (CenteredSupport.tanh_pos hv)

lemma hasDerivAt_s {v : ℝ} (hv : 0 < v) : HasDerivAt s (sd v) v := by
  have hc := ne_of_gt (Real.cosh_pos v)
  have hs := ne_of_gt (Real.sinh_pos_iff.mpr hv)
  convert (hasDerivAt_theta v).div (Real.hasDerivAt_sinh v) hs using 1 <;> try rfl
  dsimp [sd, s]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

lemma hasDerivAt_c {v : ℝ} (hv : 0 < v) : HasDerivAt c (cd v) v := by
  have hc := ne_of_gt (Real.cosh_pos v)
  have hs := ne_of_gt (Real.sinh_pos_iff.mpr hv)
  have ht := ne_of_gt (CenteredSupport.tanh_pos hv)
  convert ((hasDerivAt_theta v).pow 2).div (hasDerivAt_tanh v) ht using 1 <;> try rfl
  dsimp [cd, s]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

lemma hasDerivAt_cd {v : ℝ} (hv : 0 < v) :
    HasDerivAt cd (2*(1-s v)*sd v) v := by
  convert ((hasDerivAt_s hv).const_mul 2).sub ((hasDerivAt_s hv).pow 2) using 1 <;> try rfl
  ring

lemma cd_pos {v : ℝ} (hv : 0 < v) : 0 < cd v := by
  have hs0 := s_pos hv
  have hs1 := s_lt_one hv
  unfold cd
  nlinarith

lemma one_sub_cd (v : ℝ) : 1-cd v = (1-s v)^2 := by unfold cd; ring

lemma c_second_derivative_neg {v : ℝ} (hv : 0 < v) : deriv cd v < 0 := by
  rw [(hasDerivAt_cd hv).deriv]
  exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) (sub_pos.mpr (s_lt_one hv))) (sd_neg hv)

lemma c_strictMono : StrictMonoOn c (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi _)
  · intro v hv
    exact (hasDerivAt_c hv).continuousAt.continuousWithinAt
  · intro v hv
    rw [interior_Ioi] at hv
    rw [(hasDerivAt_c hv).deriv]
    exact cd_pos hv

lemma cd_strictAnti : StrictAntiOn cd (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi _)
  · intro v hv
    exact (hasDerivAt_cd hv).continuousAt.continuousWithinAt
  · intro v hv
    rw [interior_Ioi] at hv
    exact c_second_derivative_neg hv

lemma h_tanh_pos (v : ℝ) : 0 < h (Real.tanh v) := by
  unfold h
  apply Real.binEntropy_pos <;> linarith [Real.neg_one_lt_tanh v, Real.tanh_lt_one v]

lemma F_pos {v : ℝ} (hv : 0 < v) : 0 < F v :=
  div_pos (h_tanh_pos v) (CenteredSupport.tanh_pos hv)

lemma hasDerivAt_h_tanh (v : ℝ) :
    HasDerivAt (fun v => h (Real.tanh v)) (-v/(Real.cosh v)^2) v := by
  have hh := ((CenteredSupport.hasDerivAt_phi
    ⟨Real.neg_one_lt_tanh v, Real.tanh_lt_one v⟩).comp v (hasDerivAt_tanh v)).const_sub (Real.log 2)
  convert hh using 1 <;> try rfl
  · funext x
    simp [phi]
  · rw [CenteredSupport.g_eq_artanh ⟨Real.neg_one_lt_tanh v, Real.tanh_lt_one v⟩,
      Real.artanh_tanh]
    ring

lemma hasDerivAt_F {v : ℝ} (hv : 0 < v) :
    HasDerivAt F (-(v*Real.tanh v+h (Real.tanh v))/(Real.sinh v)^2) v := by
  have ht := ne_of_gt (CenteredSupport.tanh_pos hv)
  have hc := ne_of_gt (Real.cosh_pos v)
  have hs := ne_of_gt (Real.sinh_pos_iff.mpr hv)
  convert (hasDerivAt_h_tanh v).div (hasDerivAt_tanh v) ht using 1 <;> try rfl
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  ring

lemma F_strictAnti : StrictAntiOn F (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi _)
  · intro v hv
    exact (hasDerivAt_F hv).continuousAt.continuousWithinAt
  · intro v hv
    rw [interior_Ioi] at hv
    rw [(hasDerivAt_F hv).deriv]
    apply div_neg_of_neg_of_pos
    · have ht := CenteredSupport.tanh_pos hv
      have hh := h_tanh_pos v
      exact neg_neg_of_pos (add_pos (mul_pos hv ht) hh)
    · exact sq_pos_of_pos (Real.sinh_pos_iff.mpr hv)



lemma c_strictConcave : StrictConcaveOn ℝ (Ioi 0) c := by
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi _)
  · intro v hv
    exact (hasDerivAt_c hv).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    intro u hu v hv huv
    rw [(hasDerivAt_c hu).deriv, (hasDerivAt_c hv).deriv]
    exact cd_strictAnti hu hv huv



open Filter Topology in
lemma continuousAt_c_zero : ContinuousAt c 0 := by
  have ha : Tendsto (fun v => theta v/v) (𝓝[≠] 0) (𝓝 1) := by
    simpa [slope_fun_def_field, theta] using (hasDerivAt_theta 0).tendsto_slope
  have hb : Tendsto (fun v => Real.tanh v/v) (𝓝[≠] 0) (𝓝 1) := by
    simpa [slope_fun_def_field] using (hasDerivAt_tanh 0).tendsto_slope
  have hz : Tendsto theta (𝓝[≠] 0) (𝓝 0) := by
    simpa [theta] using continuous_theta.continuousAt.tendsto.mono_left
      (show 𝓝[≠] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hh := (hz.mul ha).div hb (by norm_num : (1:ℝ) ≠ 0)
  apply continuousAt_iff_punctured_nhds.mpr
  have heq : ∀ v : ℝ, theta v*(theta v/v)/(Real.tanh v/v) = c v := by
    intro v
    by_cases hv : v = 0
    · simp [hv, c, theta]
    · unfold c
      field_simp
  have hfun : ((fun v => theta v*(theta v/v))/(fun v => Real.tanh v/v)) = c := funext heq
  rw [hfun] at hh
  simpa [c, theta] using hh

lemma c_zero : c 0 = 0 := by simp [c, theta]

lemma continuousOn_c : ContinuousOn c (Ici 0) := by
  intro v hv
  rcases eq_or_lt_of_le (show 0 ≤ v from hv) with heq | hp
  · subst v
    exact continuousAt_c_zero.continuousWithinAt
  · exact (hasDerivAt_c hp).continuousAt.continuousWithinAt

lemma c_strictConcave_nonneg : StrictConcaveOn ℝ (Ici 0) c := by
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici _) continuousOn_c
  rw [interior_Ici]
  intro u hu v hv huv
  rw [(hasDerivAt_c hu).deriv, (hasDerivAt_c hv).deriv]
  exact cd_strictAnti hu hv huv

lemma c_div_antitone : AntitoneOn (fun v => c v/v) (Ioi 0) := by
  have hh := c_strictConcave_nonneg.concaveOn.antitoneOn_slope_gt (by simp : (0:ℝ) ∈ Ici 0)
  intro u hu v hv huv
  have h := hh (a := u) (b := v) ⟨show 0 ≤ u from (show 0 < u from hu).le, hu⟩
    ⟨show 0 ≤ v from (show 0 < v from hv).le, hv⟩ huv
  simpa [slope_def_field, c_zero] using h

lemma c_le_self {v : ℝ} (hv : 0 ≤ v) : c v ≤ v := by
  have hm : MonotoneOn (fun v => v-c v) (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _)
      (continuous_id.continuousOn.sub continuousOn_c)
    · intro v hv
      rw [interior_Ici] at hv
      exact ((hasDerivAt_id v).sub (hasDerivAt_c hv)).hasDerivWithinAt
    · intro v hv
      rw [interior_Ici] at hv
      rw [one_sub_cd]
      positivity
  have hh := hm (by simp : (0:ℝ) ∈ Ici 0) hv hv
  simpa [c_zero] using hh

end MostInformativeBit.ChannelProfiles
