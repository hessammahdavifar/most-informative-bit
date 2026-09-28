import MostInformativeBit.ChannelProfiles

/-! Exact channel estimates for the profile-rate argument. -/
namespace MostInformativeBit.ChannelBounds
open Set Real ChannelProfiles

noncomputable def q (v : ℝ) : ℝ := Real.exp (-2*v)
noncomputable def rate (v : ℝ) : ℝ := -deriv F v/F v

lemma q_pos (v : ℝ) : 0 < q v := Real.exp_pos _

lemma q_lt_one {v : ℝ} (hv : 0 < v) : q v < 1 := by
  unfold q
  rw [Real.exp_lt_one_iff]
  linarith

lemma tanh_eq_q (v : ℝ) : Real.tanh v = (1-q v)/(1+q v) := by
  rw [CenteredSupport.tanh_exp_two]
  unfold q
  rw [show -2*v = -(2*v) by ring, Real.exp_neg]
  have he := ne_of_gt (Real.exp_pos (2*v))
  field_simp

lemma h_logistic {z : ℝ} (hz : 0 < z) :
    h ((1-z)/(1+z)) = Real.log (1+z)-z/(1+z)*Real.log z := by
  have hz' := ne_of_gt hz
  have hp : 1+z ≠ 0 := by positivity
  have ha : (1-(1-z)/(1+z))/2 = z/(1+z) := by field_simp; ring
  have hb : 1-z/(1+z) = 1/(1+z) := by field_simp; ring
  unfold h Real.binEntropy
  rw [ha, hb, Real.log_inv, Real.log_inv,
    Real.log_div hz' hp, Real.log_div (by norm_num : (1:ℝ) ≠ 0) hp, Real.log_one]
  field_simp
  ring

lemma h_tanh_eq_q (v : ℝ) :
    h (Real.tanh v) = Real.log (1+q v)+2*v*q v/(1+q v) := by
  rw [tanh_eq_q, h_logistic (q_pos v)]
  have hlog : Real.log (q v) = -2*v := by rw [q, Real.log_exp]
  rw [hlog]
  ring

lemma sinh_sq_q (v : ℝ) : 4*q v*(Real.sinh v)^2 = (1-q v)^2 := by
  unfold q
  rw [show -2*v = -(v+v) by ring, Real.exp_neg, Real.exp_add, Real.sinh_eq,
    Real.exp_neg]
  have he := ne_of_gt (Real.exp_pos v)
  field_simp
  ring

/-- Algebraic step behind the manuscript's uniform lower rate bound. -/
lemma rational_rate_lower {v z L : ℝ} (hv : 0 < v) (hz : z ∈ Ioo 0 1)
    (hL : 0 < L) (hLz : L ≤ z) :
    4*v/(2*v+1) ≤ 4*z*(v+L)/((1-z)*((1+z)*L+2*v*z)) := by
  have hz0 := hz.1
  have hz1 : 0 < 1-z := sub_pos.mpr hz.2
  have hd : 0 < (1-z)*((1+z)*L+2*v*z) := by positivity
  have hvd : 0 < 2*v+1 := by positivity
  rw [div_le_div_iff₀ hvd hd]
  have hh : 0 ≤ v*(z-L)+z*(L*z*v+2*L*v+L+2*z*v^2) := by
    have : 0 ≤ z-L := sub_nonneg.mpr hLz
    positivity
  nlinarith only [hh]

lemma rate_eq_q {v : ℝ} (hv : 0 < v) :
    rate v = 4*q v*(v+Real.log (1+q v))/
      ((1-q v)*((1+q v)*Real.log (1+q v)+2*v*q v)) := by
  have hq0 := q_pos v
  have hq1 := q_lt_one hv
  have hL : 0 < Real.log (1+q v) := Real.log_pos (by linarith)
  have hh := h_tanh_pos v
  have ht := CenteredSupport.tanh_pos hv
  have hs := Real.sinh_pos_iff.mpr hv
  have hqn : q v ≠ 0 := ne_of_gt hq0
  have hp : 1+q v ≠ 0 := by positivity
  have hm : 1-q v ≠ 0 := by linarith
  have hden : (1+q v)*Real.log (1+q v)+2*v*q v ≠ 0 := by positivity
  unfold rate
  rw [(hasDerivAt_F hv).deriv]
  unfold F
  rw [tanh_eq_q, h_logistic hq0]
  have hlog : Real.log (q v) = -2*v := by rw [q, Real.log_exp]
  rw [hlog]
  have hfrac : Real.log (1+q v)-q v/(1+q v)*(-2*v) =
      ((1+q v)*Real.log (1+q v)+2*v*q v)/(1+q v) := by
    field_simp
    ring
  rw [hfrac]
  have hsq := sinh_sq_q v
  field_simp
  linear_combination -(1+q v)*(v+Real.log (1+q v))*hsq

/-- The manuscript's universal elementary lower bound on -F'/F. -/
theorem rate_lower {v : ℝ} (hv : 0 < v) : 4*v/(2*v+1) ≤ rate v := by
  rw [rate_eq_q hv]
  apply rational_rate_lower hv ⟨q_pos v, q_lt_one hv⟩
  · exact Real.log_pos (by linarith [q_pos v])
  · have hh := Real.log_le_sub_one_of_pos (by linarith [q_pos v] : 0 < 1+q v)
    linarith



/-- The sharper logarithmic rate bound, with no limit argument required. -/
theorem rate_gt_coth {v : ℝ} (hv : 0 < v) : 1/Real.tanh v < rate v := by
  have hq0 := q_pos v
  have hq1 := q_lt_one hv
  have hL : 0 < Real.log (1+q v) := Real.log_pos (by linarith)
  have hLq : Real.log (1+q v) ≤ q v := by
    have hh := Real.log_le_sub_one_of_pos (by linarith : 0 < 1+q v)
    linarith
  have hvq : 1-q v < 2*v := by
    have hh := Real.add_one_lt_exp (by linarith : -2*v ≠ 0)
    change -2*v+1 < q v at hh
    linarith
  have hmul : (1-q v)*Real.log (1+q v) < 2*v*q v := by
    have hh := mul_le_mul_of_nonneg_left hLq (by linarith : 0 ≤ 1-q v)
    have hh' := mul_lt_mul_of_pos_right hvq hq0
    linarith
  have hcert := mul_pos (sq_pos_of_pos (sub_pos.mpr hq1)) (sub_pos.mpr hmul)
  rw [rate_eq_q hv, tanh_eq_q]
  have hm : 0 < 1-q v := by linarith
  have hp : 0 < 1+q v := by positivity
  have hd : 0 < (1+q v)*Real.log (1+q v)+2*v*q v := by positivity
  rw [one_div_div]
  rw [div_lt_div_iff₀ hm (mul_pos hm hd)]
  nlinarith only [hcert]

/-- The large-v branch of the first profile-rate inequality. -/
theorem rate_angle_tail {v : ℝ} (hv : 4 ≤ v) :
    rate v-1/v > (3/2)*(1-deriv c v) := by
  have hv0 : 0 < v := by linarith
  have hbase := rate_lower hv0
  have hnum : (3:ℝ)/2+1/v < 4*v/(2*v+1) := by
    have hd : 0 < 2*v+1 := by positivity
    apply (lt_div_iff₀ hd).mpr
    have hclear : (3/2+1/v)*(2*v+1) < 4*v ↔
        (3/2*v+1)*(2*v+1) < 4*v^2 := by
      constructor <;> intro hh
      · have hh' := mul_lt_mul_of_pos_right hh hv0
        field_simp at hh'
        nlinarith only [hh']
      · apply (mul_lt_mul_iff_left₀ hv0).mp
        field_simp
        nlinarith only [hh]
    rw [hclear]
    nlinarith [sq_nonneg (v-4)]
  have hcd := cd_pos hv0
  rw [(hasDerivAt_c hv0).deriv]
  linarith



open Filter Topology

lemma tendsto_q_atTop : Tendsto q atTop (𝓝 0) := by
  have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2) tendsto_id)
  change Tendsto (fun v : ℝ => Real.exp (-2*v)) atTop (𝓝 0)
  simpa only [Function.comp_def, neg_mul, id_eq] using hh

lemma tendsto_tanh_atTop : Tendsto Real.tanh atTop (𝓝 1) := by
  have hh := ((tendsto_const_nhds (x := (1:ℝ))).sub tendsto_q_atTop).div
    (tendsto_const_nhds.add tendsto_q_atTop) (by norm_num : (1:ℝ)+0 ≠ 0)
  convert hh using 1 <;> try rfl
  · exact funext tanh_eq_q
  · norm_num

lemma tendsto_F_atTop : Tendsto F atTop (𝓝 0) := by
  have hh : Continuous h := by unfold h; fun_prop
  have hlim : Tendsto (fun v => h (Real.tanh v)) atTop (𝓝 0) := by
    convert hh.continuousAt.tendsto.comp tendsto_tanh_atTop using 1 <;> try rfl
    simp [h]
  convert hlim.div tendsto_tanh_atTop (by norm_num : (1:ℝ) ≠ 0) using 1 <;> try rfl
  norm_num

lemma tendsto_F_zero_right : Tendsto F (𝓝[>] 0) atTop := by
  have ht : Tendsto Real.tanh (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using continuous_tanh.continuousAt.tendsto.mono_left
        (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with v hv
      exact CenteredSupport.tanh_pos hv
  have hc : Continuous (fun v => h (Real.tanh v)) :=
    continuous_iff_continuousAt.mpr fun v => (hasDerivAt_h_tanh v).continuousAt
  have hh : Tendsto (fun v => h (Real.tanh v)) (𝓝[>] 0) (𝓝 (Real.log 2)) := by
    simpa [h, one_div] using hc.continuousAt.tendsto.mono_left
      (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  change Tendsto (fun v => h (Real.tanh v)/Real.tanh v) (𝓝[>] 0) atTop
  simpa only [div_eq_mul_inv, Pi.inv_apply] using
    Tendsto.pos_mul_atTop (Real.log_pos (by norm_num : (1:ℝ) < 2)) hh
      ht.inv_tendsto_nhdsGT_zero



/-- Every positive entropy budget determines a unique positive channel height. -/
theorem existsUnique_height {budget : ℝ} (hb : 0 < budget) :
    ∃! v : ℝ, 0 < v ∧ F v = budget := by
  have haev : ∀ᶠ v : ℝ in 𝓝[>] 0, 0 < v := self_mem_nhdsWithin
  obtain ⟨a, ha, hFa⟩ := (Filter.Eventually.and haev
    (tendsto_F_zero_right.eventually_gt_atTop budget)).exists
  obtain ⟨b, hab, hFb⟩ := ((eventually_gt_atTop a).and
    (tendsto_F_atTop.eventually_lt_const hb)).exists
  have hc : ContinuousOn F (Icc a b) := by
    intro v hv
    exact (hasDerivAt_F (lt_of_lt_of_le ha hv.1)).continuousAt.continuousWithinAt
  obtain ⟨v, hv, hFv⟩ := intermediate_value_Icc' hab.le hc ⟨hFb.le, hFa.le⟩
  have hv0 := lt_of_lt_of_le ha hv.1
  refine ⟨v, ⟨hv0, hFv⟩, ?_⟩
  intro w hw
  exact F_strictAnti.injOn hw.1 hv0 (hw.2.trans hFv.symm)



/-- Derivative comparison at zero, reused for elementary trigonometric bounds. -/
lemma nonneg_of_deriv_nonneg {f f' : ℝ → ℝ}
    (hd : ∀ v, HasDerivAt f (f' v) v) (h0 : f 0 = 0)
    (hp : ∀ v, 0 ≤ v → 0 ≤ f' v) {v : ℝ} (hv : 0 ≤ v) : 0 ≤ f v := by
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _)
    · intro x _; exact (hd x).continuousAt.continuousWithinAt
    · intro x _; exact (hd x).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact hp x hx.le
  have hh := hm (by simp : (0:ℝ) ∈ Ici 0) hv hv
  rwa [h0] at hh

lemma angular_numerator_nonneg {t : ℝ} (ht : t ∈ Icc 0 (Real.pi/2)) :
    0 ≤ 2*Real.sin t+Real.sin t*Real.cos t-t-2*t*Real.cos t := by
  let f : ℝ → ℝ := fun t => 2*Real.sin t+Real.sin t*Real.cos t-t-2*t*Real.cos t
  have hd (t : ℝ) : HasDerivAt f (2*Real.sin t*(t-Real.sin t)) t := by
    convert (((((Real.hasDerivAt_sin t).const_mul 2).add
      ((Real.hasDerivAt_sin t).mul (Real.hasDerivAt_cos t))).sub (hasDerivAt_id t)).sub
      (((hasDerivAt_id t).const_mul 2).mul (Real.hasDerivAt_cos t))) using 1 <;> try rfl
    dsimp
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hm : MonotoneOn f (Icc 0 (Real.pi/2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    · intro t _; exact (hd t).continuousAt.continuousWithinAt
    · intro t _; exact (hd t).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have hs := (CenteredSupport.trig_domain ht).1.1
      have hh := Real.sin_le ht.1.le
      positivity
  have hh := hm ⟨le_rfl, Real.pi_div_two_pos.le⟩ ht ht.1
  simpa [f] using hh

lemma angular_lower {t : ℝ} (ht : t ∈ Icc 0 (Real.pi/2)) :
    3*Real.sin t ≤ t*(2+Real.cos t) := by
  let f : ℝ → ℝ := fun t => t*(2+Real.cos t)-3*Real.sin t
  let f' : ℝ → ℝ := fun t => 2-2*Real.cos t-t*Real.sin t
  have h1 (t : ℝ) : HasDerivAt f (f' t) t := by
    convert (((hasDerivAt_id t).mul ((Real.hasDerivAt_cos t).const_add 2)).sub
      ((Real.hasDerivAt_sin t).const_mul 3)) using 1 <;> try rfl
    dsimp [f']
    ring
  have h2 (t : ℝ) : HasDerivAt f' (Real.sin t-t*Real.cos t) t := by
    convert ((((Real.hasDerivAt_cos t).const_mul 2).const_sub 2).sub
      ((hasDerivAt_id t).mul (Real.hasDerivAt_sin t))) using 1 <;> try rfl
    dsimp
    ring
  have h3 (t : ℝ) : HasDerivAt (fun t => Real.sin t-t*Real.cos t) (t*Real.sin t) t := by
    convert (Real.hasDerivAt_sin t).sub ((hasDerivAt_id t).mul (Real.hasDerivAt_cos t))
      using 1 <;> try rfl
    dsimp
    ring
  have mono_step {f f' : ℝ → ℝ} (hd : ∀ t, HasDerivAt f (f' t) t)
      (h0 : f 0 = 0) (hp : ∀ t ∈ Ioo 0 (Real.pi/2), 0 ≤ f' t) :
      ∀ t ∈ Icc 0 (Real.pi/2), 0 ≤ f t := by
    have hm : MonotoneOn f (Icc 0 (Real.pi/2)) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      · intro t _; exact (hd t).continuousAt.continuousWithinAt
      · intro t _; exact (hd t).hasDerivWithinAt
      · simpa only [interior_Icc] using hp
    intro t ht
    have hh := hm ⟨le_rfl, Real.pi_div_two_pos.le⟩ ht ht.1
    rwa [h0] at hh
  have hp3 := mono_step h3 (by simp) (fun t ht =>
    mul_nonneg ht.1.le (CenteredSupport.trig_domain ht).1.1.le)
  have hp2 := mono_step h2 (by simp [f']) (fun t ht => hp3 t ⟨ht.1.le, ht.2.le⟩)
  have hp1 := mono_step h1 (by simp [f]) (fun t ht => hp2 t ⟨ht.1.le, ht.2.le⟩)
  exact sub_nonneg.mp (hp1 t ht)

lemma angular_upper {t : ℝ} (ht : t ∈ Icc 0 (Real.pi/2)) :
    t*(2+Real.cos t) ≤ Real.pi*Real.sin t := by
  by_cases hz : t = 0
  · simp [hz]
  have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hz)
  let f : ℝ → ℝ := fun t => t*(2+Real.cos t)/Real.sin t
  have hd (t : ℝ) (ht : t ∈ Ioc 0 (Real.pi/2)) : HasDerivAt f
      ((2*Real.sin t+Real.sin t*Real.cos t-t-2*t*Real.cos t)/(Real.sin t)^2) t := by
    have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
    convert ((hasDerivAt_id t).mul ((Real.hasDerivAt_cos t).const_add 2)).div
      (Real.hasDerivAt_sin t) (ne_of_gt hs) using 1 <;> try rfl
    apply congrArg (fun z : ℝ => z/(Real.sin t)^2)
    dsimp
    linear_combination t*(Real.sin_sq_add_cos_sq t)
  have hm : MonotoneOn f (Ioc 0 (Real.pi/2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc _ _)
    · intro t ht; exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioc] at ht
      exact (hd t ⟨ht.1,ht.2.le⟩).hasDerivWithinAt
    · intro t ht
      rw [interior_Ioc] at ht
      exact div_nonneg (angular_numerator_nonneg ⟨ht.1.le,ht.2.le⟩) (sq_nonneg _)
  have hh := hm ⟨ht0,ht.2⟩ ⟨Real.pi_div_two_pos,le_rfl⟩ ht.2
  dsimp [f] at hh
  simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, add_zero, div_one] at hh
  have hs := Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [ht.2, Real.pi_pos])
  rw [div_le_iff₀ hs] at hh
  nlinarith only [hh]

/-- Shafer-Fink brackets used in profile-rates.tex. -/
theorem arcsin_brackets {z : ℝ} (hz : z ∈ Icc 0 1) :
    3*z/(2+Real.sqrt (1-z^2)) ≤ Real.arcsin z ∧
    Real.arcsin z ≤ Real.pi*z/(2+Real.sqrt (1-z^2)) := by
  have ht : Real.arcsin z ∈ Icc 0 (Real.pi/2) :=
    ⟨Real.arcsin_nonneg.mpr hz.1, Real.arcsin_le_pi_div_two z⟩
  have hl := angular_lower ht
  have hu := angular_upper ht
  rw [Real.sin_arcsin (by linarith [hz.1]) hz.2, Real.cos_arcsin] at hl hu
  have hd : 0 < 2+Real.sqrt (1-z^2) := by positivity
  constructor
  · exact (div_le_iff₀ hd).mpr hl
  · exact (le_div_iff₀ hd).mpr hu



lemma sinh_cosh_gap {v : ℝ} (hv : 0 ≤ v) :
    v^3/3 ≤ v*Real.cosh v-Real.sinh v := by
  have hd (v : ℝ) : HasDerivAt (fun v => v*Real.cosh v-Real.sinh v-v^3/3)
      (v*(Real.sinh v-v)) v := by
    convert (((hasDerivAt_id v).mul (Real.hasDerivAt_cosh v)).sub
      (Real.hasDerivAt_sinh v)).sub (((hasDerivAt_id v).pow 3).div_const 3)
      using 1 <;> try rfl
    dsimp
    ring
  have hh := nonneg_of_deriv_nonneg hd (by simp) (fun v hv =>
    mul_nonneg hv (sub_nonneg.mpr (Real.self_le_sinh_iff.mpr hv))) hv
  linarith

lemma cosh_scale_numerator_nonneg {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ v*Real.sinh v-2*Real.cosh v+2 := by
  have hd (v : ℝ) : HasDerivAt (fun v => v*Real.sinh v-2*Real.cosh v+2)
      (v*Real.cosh v-Real.sinh v) v := by
    convert ((((hasDerivAt_id v).mul (Real.hasDerivAt_sinh v)).sub
      ((Real.hasDerivAt_cosh v).const_mul 2)).add_const 2) using 1 <;> try rfl
    dsimp
    ring
  apply nonneg_of_deriv_nonneg hd (by simp) _ hv
  intro v hv
  have hh := sinh_cosh_gap hv
  have : 0 ≤ v^3 := pow_nonneg hv 3
  linarith

lemma cosh_scale_monotone : MonotoneOn (fun v => (Real.cosh v-1)/v^2) (Ioi 0) := by
  have hd (v : ℝ) (hv : 0 < v) : HasDerivAt (fun v => (Real.cosh v-1)/v^2)
      ((v*Real.sinh v-2*Real.cosh v+2)/v^3) v := by
    convert ((Real.hasDerivAt_cosh v).sub_const 1).div ((hasDerivAt_id v).pow 2)
      (ne_of_gt (sq_pos_of_pos hv)) using 1 <;> try rfl
    dsimp
    field_simp
    ring
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi _)
  · intro v hv; exact (hd v hv).continuousAt.continuousWithinAt
  · intro v hv
    rw [interior_Ioi] at hv
    exact (hd v hv).hasDerivWithinAt
  · intro v hv
    rw [interior_Ioi] at hv
    exact div_nonneg (cosh_scale_numerator_nonneg hv.le) (pow_nonneg hv.le 3)

lemma cosh_quadratic_of_endpoint {v b a : ℝ} (hv : 0 ≤ v) (hb : 0 < b) (hvb : v ≤ b)
    (hbound : Real.cosh b ≤ 1+a*b^2) : Real.cosh v ≤ 1+a*v^2 := by
  rcases eq_or_lt_of_le hv with heq | hp
  · subst v; simp
  have hh := cosh_scale_monotone hp hb hvb
  have hh' : (Real.cosh b-1)/b^2 ≤ a := (div_le_iff₀ (sq_pos_of_pos hb)).mpr (by linarith)
  have := (div_le_iff₀ (sq_pos_of_pos hp)).mp (le_trans hh hh')
  linarith

lemma sinh_scale_monotone : MonotoneOn (fun v => Real.sinh v/v) (Ioi 0) := by
  have hd (v : ℝ) (hv : 0 < v) : HasDerivAt (fun v => Real.sinh v/v)
      ((v*Real.cosh v-Real.sinh v)/v^2) v := by
    convert (Real.hasDerivAt_sinh v).div (hasDerivAt_id v) (ne_of_gt hv) using 1 <;> try rfl
    dsimp
    ring
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi _)
  · intro v hv; exact (hd v hv).continuousAt.continuousWithinAt
  · intro v hv
    rw [interior_Ioi] at hv
    exact (hd v hv).hasDerivWithinAt
  · intro v hv
    rw [interior_Ioi] at hv
    apply div_nonneg _ (sq_nonneg _)
    have hh := sinh_cosh_gap hv.le
    have : 0 ≤ v^3 := pow_nonneg hv.le 3
    linarith

lemma exp_one_bounds : (8:ℝ)/3 < Real.exp 1 ∧ Real.exp 1 < 11/4 := by
  have hl := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 1) 6
  have hu := Real.exp_bound' (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) ≤ 1)
    (by norm_num : 0 < (6:ℕ))
  norm_num [Finset.sum_range_succ, Nat.factorial] at hl hu
  constructor <;> linarith

lemma cosh_one_bound : Real.cosh 1 < 25/16 := by
  obtain ⟨hl,hu⟩ := exp_one_bounds
  have hi : 1/Real.exp 1 < (3:ℝ)/8 := (div_lt_iff₀ (Real.exp_pos 1)).mpr (by linarith)
  rw [Real.cosh_eq, Real.exp_neg]
  simp only [one_div] at hi
  linarith

lemma sinh_one_bound : Real.sinh 1 < 6/5 := by
  obtain ⟨hl,hu⟩ := exp_one_bounds
  have hi : (4:ℝ)/11 < 1/Real.exp 1 := (lt_div_iff₀ (Real.exp_pos 1)).mpr (by linarith)
  rw [Real.sinh_eq, Real.exp_neg]
  simp only [one_div] at hi
  linarith

lemma cosh_two_bound : Real.cosh 2 < 4 := by
  have hh := Real.cosh_two_mul (1:ℝ)
  norm_num at hh
  have h := cosh_one_bound
  have hp := Real.cosh_pos 1
  nlinarith [Real.cosh_sq_sub_sinh_sq (1:ℝ)]

lemma cosh_four_bound : Real.cosh 4 < 33 := by
  have hh := Real.cosh_two_mul (2:ℝ)
  norm_num at hh
  have h := cosh_two_bound
  have hp := Real.cosh_pos 2
  nlinarith [Real.cosh_sq_sub_sinh_sq (2:ℝ)]

lemma cosh_small {v : ℝ} (hv : v ∈ Icc 0 1) : Real.cosh v ≤ 1+3*v^2/5 := by
  convert cosh_quadratic_of_endpoint hv.1 (by norm_num : (0:ℝ) < 1) hv.2
    (show Real.cosh 1 ≤ 1+(3/5:ℝ)*1^2 by linarith [cosh_one_bound]) using 1 <;> ring

lemma cosh_medium {v : ℝ} (hv : v ∈ Icc 0 2) : Real.cosh v ≤ 1+3*v^2/4 := by
  convert cosh_quadratic_of_endpoint hv.1 (by norm_num : (0:ℝ) < 2) hv.2
    (show Real.cosh 2 ≤ 1+(3/4:ℝ)*2^2 by linarith [cosh_two_bound]) using 1 <;> ring

lemma cosh_large {v : ℝ} (hv : v ∈ Icc 0 4) : Real.cosh v ≤ 1+2*v^2 := by
  exact cosh_quadratic_of_endpoint hv.1 (by norm_num : (0:ℝ) < 4) hv.2
    (show Real.cosh 4 ≤ 1+(2:ℝ)*4^2 by linarith [cosh_four_bound])

lemma sinh_small {v : ℝ} (hv : v ∈ Ioc 0 1) : Real.sinh v < 6*v/5 := by
  have hh := sinh_scale_monotone hv.1 (by norm_num : (0:ℝ) < 1) hv.2
  simp only [div_one] at hh
  have hh' := (div_lt_iff₀ hv.1).mp (lt_of_le_of_lt hh sinh_one_bound)
  linarith



lemma s_lower {v : ℝ} (hv : 0 < v) : 3/(2*Real.cosh v+1) ≤ s v := by
  have hc := Real.cosh_pos v
  have hs := Real.sinh_pos_iff.mpr hv
  have hh := (arcsin_brackets
    ⟨(CenteredSupport.tanh_pos hv).le, (Real.tanh_lt_one v).le⟩).1
  have hr : Real.sqrt (1-(Real.tanh v)^2) = 1/Real.cosh v := by
    rw [cosh_eq_inv_sqrt, one_div_div, div_one]
  rw [hr, Real.tanh_eq_sinh_div_cosh] at hh
  have heq : 3*(Real.sinh v/Real.cosh v)/(2+1/Real.cosh v) =
      3*Real.sinh v/(2*Real.cosh v+1) := by field_simp
  rw [heq, ← Real.tanh_eq_sinh_div_cosh v] at hh
  change 3*Real.sinh v/(2*Real.cosh v+1) ≤ theta v at hh
  unfold s
  rw [div_le_div_iff₀ (by positivity : 0 < 2*Real.cosh v+1) hs]
  exact (div_le_iff₀ (by positivity : 0 < 2*Real.cosh v+1)).mp hh

lemma one_sub_s_le {v w : ℝ} (hv : 0 < v) (hw : 0 ≤ w)
    (hc : Real.cosh v ≤ 1+w) : 1-s v ≤ 2*w/(3+2*w) := by
  have hh := s_lower hv
  have hd := Real.cosh_pos v
  have hfrac : 3/(3+2*w) ≤ 3/(2*Real.cosh v+1) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    linarith
  have hs := le_trans hfrac hh
  have heq : 1-3/(3+2*w) = 2*w/(3+2*w) := by field_simp; ring
  rw [← heq]
  linarith

lemma one_sub_s_small {v : ℝ} (hv : v ∈ Ioc 0 1) :
    1-s v ≤ 2*v^2/(5+2*v^2) := by
  have hh := one_sub_s_le hv.1 (show 0 ≤ 3*v^2/5 by positivity) (cosh_small ⟨hv.1.le,hv.2⟩)
  convert hh using 1 <;> try rfl
  field_simp

lemma one_sub_s_medium {v : ℝ} (hv : v ∈ Ioc 0 2) :
    1-s v ≤ v^2/(2+v^2) := by
  have hh := one_sub_s_le hv.1 (show 0 ≤ 3*v^2/4 by positivity) (cosh_medium ⟨hv.1.le,hv.2⟩)
  convert hh using 1 <;> try rfl
  field_simp
  ring

lemma one_sub_s_large {v : ℝ} (hv : v ∈ Ioc 0 4) :
    1-s v ≤ 4*v^2/(3+4*v^2) := by
  have hh := one_sub_s_le hv.1 (show 0 ≤ 2*v^2 by positivity) (cosh_large ⟨hv.1.le,hv.2⟩)
  convert hh using 1 <;> ring

lemma coth_sub_inv_gt_quarter {v : ℝ} (hv : v ∈ Ioc 0 1) :
    v/4 < 1/Real.tanh v-1/v := by
  have hs := Real.sinh_pos_iff.mpr hv.1
  have hh := sinh_cosh_gap hv.1.le
  have hu := sinh_small hv
  have hmul := mul_lt_mul_of_pos_right hu (sq_pos_of_pos hv.1)
  have hv3 : 0 < v^3 := pow_pos hv.1 3
  rw [Real.tanh_eq_sinh_div_cosh, one_div_div]
  apply (lt_sub_iff_add_lt).mpr
  apply (lt_div_iff₀ hs).mpr
  apply (mul_lt_mul_iff_right₀ hv.1).mp
  have hn : v ≠ 0 := ne_of_gt hv.1
  have heq : v*((v/4+1/v)*Real.sinh v) = (v^2/4+1)*Real.sinh v := by
    field_simp [hn]
    <;> ring
  rw [heq]
  nlinarith only [hh, hmul, hv3]

lemma small_rate_algebra {v : ℝ} (hv : v ∈ Ioc 0 1) :
    2*(2*v^2/(5+2*v^2))^2 < v/4 := by
  have hv0 := hv.1
  have hv1 := hv.2
  have hd : 0 < (5+2*v^2)^2 := by positivity
  rw [div_pow, ← mul_div_assoc, div_lt_iff₀ hd]
  have h2 : v^2 ≤ 1 := by nlinarith
  have h3 : v^3 ≤ v^2 := by nlinarith [mul_nonneg (sq_nonneg v) (sub_nonneg.mpr hv1)]
  have hpoly : 0 < (5+2*v^2)^2-32*v^3 := by nlinarith [sq_nonneg (v^2)]
  have hh := mul_pos hv0 hpoly
  nlinarith only [hh]

lemma medium_rate_algebra {v : ℝ} (hv : v ∈ Icc 1 2) :
    2*(v^2/(2+v^2))^2 < 4*v/(2*v+1)-1/v := by
  have hv0 : 0 < v := by linarith [hv.1]
  have hq : 3 ≤ 15*v-4*v^2-8 := by
    have hh := mul_nonneg (sub_nonneg.mpr hv.1) (sub_nonneg.mpr hv.2)
    nlinarith
  have hp : 0 < v^3*(15*v-4*v^2-8)+4*(3*v+1)*(v-1) := by
    have : 0 ≤ v-1 := sub_nonneg.mpr hv.1
    positivity
  have hd : 0 < v*(2*v+1)*(2+v^2)^2 := by positivity
  apply (mul_lt_mul_iff_right₀ hd).mp
  field_simp
  nlinarith only [hp]

lemma large_rate_algebra {v : ℝ} (hv : v ∈ Icc 2 4) :
    (3/2)*(4*v^2/(3+4*v^2))^2 < 4*v/(2*v+1)-1/v := by
  have hv0 : 0 < v := by linarith [hv.1]
  have h2 : 0 ≤ v-2 := sub_nonneg.mpr hv.1
  have h3 : 0 ≤ v-(3:ℝ)/2 := by linarith [hv.1]
  have h23 : 0 ≤ 2*v-3 := by linarith [hv.1]
  have hq : 0 < 4*v^2-6*v-3 := by nlinarith [sq_nonneg (v-2), hv.1]
  have hp : 0 < 16*v^4*(v-2)*(v-3/2)+16*v^3*(2*v-3)+3*(4*v^2-6*v-3) := by positivity
  have hd : 0 < v*(2*v+1)*(3+4*v^2)^2 := by positivity
  apply (mul_lt_mul_iff_right₀ hd).mp
  field_simp
  nlinarith only [hp]

/-- The coefficient-two inequality, over its full real domain. -/
theorem rate_angle_two {v : ℝ} (hv : v ∈ Ioc 0 2) :
    2*(1-deriv c v) < rate v-1/v := by
  rw [(hasDerivAt_c hv.1).deriv, one_sub_cd]
  have hs : 0 ≤ 1-s v := sub_nonneg.mpr (s_lt_one hv.1).le
  rcases le_total v 1 with hsmall | hmedium
  · have hb := one_sub_s_small ⟨hv.1,hsmall⟩
    have hsq := pow_le_pow_left₀ hs hb 2
    have ha := small_rate_algebra ⟨hv.1,hsmall⟩
    have hh := coth_sub_inv_gt_quarter ⟨hv.1,hsmall⟩
    have hq := rate_gt_coth hv.1
    linarith
  · have hb := one_sub_s_medium hv
    have hsq := pow_le_pow_left₀ hs hb 2
    have ha := medium_rate_algebra ⟨hmedium,hv.2⟩
    have hh := rate_lower hv.1
    linarith

/-- The coefficient-three-halves inequality, for every positive real v. -/
theorem rate_angle_three_halves {v : ℝ} (hv : 0 < v) :
    (3/2)*(1-deriv c v) < rate v-1/v := by
  rcases le_total v 2 with hsmall | hlarge
  · have hh := rate_angle_two ⟨hv,hsmall⟩
    rw [(hasDerivAt_c hv).deriv, one_sub_cd] at hh ⊢
    nlinarith [sq_nonneg (1-s v)]
  · rcases le_total v 4 with hmedium | htail
    · rw [(hasDerivAt_c hv).deriv, one_sub_cd]
      have hs : 0 ≤ 1-s v := sub_nonneg.mpr (s_lt_one hv).le
      have hb := one_sub_s_large ⟨hv,hmedium⟩
      have hsq := pow_le_pow_left₀ hs hb 2
      have ha := large_rate_algebra ⟨hlarge,hmedium⟩
      have hh := rate_lower hv
      linarith
    · exact rate_angle_tail htail

end MostInformativeBit.ChannelBounds
