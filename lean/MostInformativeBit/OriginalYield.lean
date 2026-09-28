import MostInformativeBit.ChannelBounds

/-! Endpoint principle for the original yield, `source/original-yield.tex`.

* `endpoint_principle` (general, exact hypotheses): if `D = vJ' - J > 0`, `J'' > 0` and the
  shape bound `-c''·D/J'' - (c - v c') < A₀/r` hold on `v > 0`, then
  `Y_P(v) = (r c(v) + A₀ + A₁ J(v))/v` has no interior maximum on `(0,∞)`.
* `shape_of_bounds`: the three curvature facts `D/J'' < v/2`, `c - vc' ≥ v² k/5`,
  `0 < k < 1/2` (with `k = -c''`) imply the shape bound `< 5/32`.
* `k_pos`, `k_le`: `0 < k ≤ tanh³ v / 2 < 1/2` for the actual angular profile.
-/

namespace MostInformativeBit.OriginalYield

open Set Real MostInformativeBit.ChannelProfiles

/-! ### General endpoint principle -/

theorem endpoint_principle {Jf J1 J2 cf c1 c2 : ℝ → ℝ} {r A0 A1 : ℝ} (hr : 0 < r)
    (hJ : ∀ v, 0 < v → HasDerivAt Jf (J1 v) v) (hJ1 : ∀ v, 0 < v → HasDerivAt J1 (J2 v) v)
    (hc : ∀ v, 0 < v → HasDerivAt cf (c1 v) v) (hc1 : ∀ v, 0 < v → HasDerivAt c1 (c2 v) v)
    (hD : ∀ v, 0 < v → 0 < v * J1 v - Jf v) (hJ2 : ∀ v, 0 < v → 0 < J2 v)
    (hshape : ∀ v, 0 < v →
      -c2 v * (v * J1 v - Jf v) / J2 v - (cf v - v * c1 v) < A0 / r)
    {a x b : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) :
    (r * cf x + A0 + A1 * Jf x) / x ≤
      max ((r * cf a + A0 + A1 * Jf a) / a) ((r * cf b + A0 + A1 * Jf b) / b) := by
  set Y : ℝ → ℝ := fun v => (r * cf v + A0 + A1 * Jf v) / v with hY
  set Φ : ℝ → ℝ := fun v => (A0 + r * (cf v - v * c1 v)) / (v * J1 v - Jf v) with hΦ
  -- derivative of Y has the sign of A1 - Φ
  have hYd : ∀ v, 0 < v → HasDerivAt Y
      ((v * J1 v - Jf v) * (A1 - Φ v) / v ^ 2) v := by
    intro v hv
    have hn := (((hc v hv).const_mul r).add_const A0).add ((hJ v hv).const_mul A1)
    have hq := hn.div (hasDerivAt_id' v) hv.ne'
    refine hq.congr_deriv ?_
    have hDv := (hD v hv).ne'
    have hDv' : J1 v * v - Jf v ≠ 0 := by rwa [mul_comm] at hDv
    simp only [hΦ, Pi.add_apply]
    field_simp
    ring
  -- Φ is antitone
  have hΦd : ∀ v, 0 < v → HasDerivAt Φ
      ((r * (-(v * c2 v)) * (v * J1 v - Jf v) - (A0 + r * (cf v - v * c1 v)) * (v * J2 v)) /
        (v * J1 v - Jf v) ^ 2) v := by
    intro v hv
    have hnum := ((hc v hv).sub ((hasDerivAt_id' v).mul (hc1 v hv))).const_mul r |>.const_add A0
    have hden := ((hasDerivAt_id' v).mul (hJ1 v hv)).sub (hJ v hv)
    have hq := hnum.div hden (hD v hv).ne'
    refine hq.congr_deriv ?_
    simp only [Pi.sub_apply, Pi.mul_apply]
    ring
  have hΦanti : AntitoneOn Φ (Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · intro v hv; exact (hΦd v hv).continuousAt.continuousWithinAt
    · rw [interior_Ioi]; intro v hv
      exact (hΦd v hv).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]; intro v hv
      rw [(hΦd v hv).deriv]
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
      have hs := hshape v hv
      have hj := hJ2 v hv
      have hd := hD v hv
      rw [sub_lt_iff_lt_add, div_lt_iff₀ hj] at hs
      have hs3 : r * (-c2 v * (v * J1 v - Jf v)) <
          (A0 + r * (cf v - v * c1 v)) * J2 v := by
        have h := mul_lt_mul_of_pos_left hs hr
        have e : r * ((A0 / r + (cf v - v * c1 v)) * J2 v) =
            (A0 + r * (cf v - v * c1 v)) * J2 v := by field_simp
        linarith
      nlinarith [mul_lt_mul_of_pos_left hs3 hv]
  -- no interior maximum by the mean value theorem
  by_contra hcon
  push Not at hcon
  have hya : Y a < Y x := lt_of_le_of_lt (le_max_left _ _) hcon
  have hyb : Y b < Y x := lt_of_le_of_lt (le_max_right _ _) hcon
  have hax' : a < x := lt_of_le_of_ne hax (by rintro rfl; exact lt_irrefl _ hya)
  have hxb' : x < b := lt_of_le_of_ne hxb (by rintro rfl; exact lt_irrefl _ hyb)
  have cont : ∀ u w, 0 < u → ContinuousOn Y (Icc u w) := fun u w hu z hz =>
    (hYd z (by linarith [hz.1])).continuousAt.continuousWithinAt
  obtain ⟨ξ₁, hξ₁, e₁⟩ := exists_hasDerivAt_eq_slope Y _ hax' (cont a x ha)
    (fun z hz => hYd z (by linarith [hz.1]))
  obtain ⟨ξ₂, hξ₂, e₂⟩ := exists_hasDerivAt_eq_slope Y _ hxb' (cont x b (by linarith))
    (fun z hz => hYd z (by linarith [hz.1]))
  have hξ₁0 : 0 < ξ₁ := by linarith [hξ₁.1]
  have hξ₂0 : 0 < ξ₂ := by linarith [hξ₂.1, hξ₁.2]
  have p1 : 0 < (ξ₁ * J1 ξ₁ - Jf ξ₁) * (A1 - Φ ξ₁) / ξ₁ ^ 2 := by
    rw [e₁]; exact div_pos (by linarith) (by linarith)
  have p2 : (ξ₂ * J1 ξ₂ - Jf ξ₂) * (A1 - Φ ξ₂) / ξ₂ ^ 2 < 0 := by
    rw [e₂]; exact div_neg_of_neg_of_pos (by linarith) (by linarith)
  have q1 : 0 < A1 - Φ ξ₁ := by
    have := (div_pos_iff_of_pos_right (sq_pos_of_pos hξ₁0)).mp p1
    exact (pos_iff_pos_of_mul_pos this).mp (hD ξ₁ hξ₁0)
  have q2 : A1 - Φ ξ₂ < 0 := by
    by_contra hq; push Not at hq
    have := div_nonneg (mul_nonneg (hD ξ₂ hξ₂0).le hq) (sq_nonneg ξ₂)
    linarith
  have hle := hΦanti hξ₁0 hξ₂0 (by linarith [hξ₁.2, hξ₂.1])
  linarith

/-! ### Combination of the three curvature facts -/

theorem shape_of_bounds {k ratio gap v : ℝ} (hk0 : 0 < k) (hk1 : k < 1/2)
    (hratio : ratio < v / 2) (hgap : v ^ 2 / 5 * k ≤ gap) :
    k * ratio - gap < 5/32 := by
  have h1 : k * ratio < k * (v / 2) := mul_lt_mul_of_pos_left hratio hk0
  have h2 : k * (v / 2 - v ^ 2 / 5) ≤ k * (5/16) :=
    mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (v - 5/4)]) hk0.le
  nlinarith

/-! ### The angular curvature `k = -c''` -/

noncomputable def k (v : ℝ) : ℝ := -(2 * (1 - s v) * sd v)

theorem k_pos {v : ℝ} (hv : 0 < v) : 0 < k v := by
  have h1 := s_lt_one hv
  have h2 := sd_neg hv
  unfold k
  nlinarith

theorem one_sub_sech_sq (v : ℝ) : 1 - (1 / Real.cosh v) ^ 2 = Real.tanh v ^ 2 := by
  have hc := Real.cosh_pos v
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  nlinarith [Real.cosh_sq_sub_sinh_sq v]

theorem k_le {v : ℝ} (hv : 0 < v) : k v ≤ Real.tanh v ^ 3 / 2 := by
  have ht := CenteredSupport.tanh_pos hv
  have e : k v = 2 * ((1 - s v) * (s v - (1 / Real.cosh v) ^ 2)) / Real.tanh v := by
    unfold k sd; field_simp; ring
  have amgm : (1 - s v) * (s v - (1 / Real.cosh v) ^ 2) ≤ Real.tanh v ^ 4 / 4 := by
    have hsum := one_sub_sech_sq v
    nlinarith [sq_nonneg ((1 - s v) - (s v - (1 / Real.cosh v) ^ 2))]
  rw [e, div_le_iff₀ ht]
  nlinarith

theorem k_lt_half {v : ℝ} (hv : 0 < v) : k v < 1/2 := by
  have h := k_le hv
  have ht0 := CenteredSupport.tanh_pos hv
  have ht1 := Real.tanh_lt_one v
  have : Real.tanh v ^ 3 < 1 := by
    calc Real.tanh v ^ 3 < 1 ^ 3 := by gcongr
      _ = 1 := by norm_num
  linarith


/-! ### Angular curvature scaling `c - v c' ≥ v² k / 5` (manuscript (angle-curvature-scaling)) -/

open Filter Topology

/-- Second derivative of `s = θ/sinh`: `s'' = -2τ² - s'(1+τ²)/tanh`, `τ = sech`. -/
noncomputable def sdd (v : ℝ) : ℝ :=
  -2 * (1 / Real.cosh v) ^ 2 - sd v * (1 + (1 / Real.cosh v) ^ 2) / Real.tanh v

theorem hasDerivAt_sech_sq (v : ℝ) :
    HasDerivAt (fun v => (1 / Real.cosh v) ^ 2) (-2 * (1 / Real.cosh v) ^ 2 * Real.tanh v) v := by
  have hc := (Real.cosh_pos v).ne'
  have h1 := ((hasDerivAt_const v (1:ℝ)).div (Real.hasDerivAt_cosh v) hc).pow 2
  refine h1.congr_deriv ?_
  simp only [Pi.div_apply]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  norm_num [hc]
  ring

theorem hasDerivAt_sd {v : ℝ} (hv : 0 < v) : HasDerivAt sd (sdd v) v := by
  have ht := (CenteredSupport.tanh_pos hv).ne'
  have hc := (Real.cosh_pos v).ne'
  have hq := ((hasDerivAt_sech_sq v).sub (hasDerivAt_s hv)).div (hasDerivAt_tanh v) ht
  refine hq.congr_deriv ?_
  unfold sdd
  have e : (1 / Real.cosh v) ^ 2 - s v = sd v * Real.tanh v := by
    unfold sd; field_simp
  simp only [Pi.sub_apply]
  rw [e]
  field_simp
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  ring

/-- Manuscript: `v w'' - w' > 0` for `w = s`, i.e. `s' ≤ v s''`. -/
theorem sd_le_v_sdd {v : ℝ} (hv : 0 < v) : sd v ≤ v * sdd v := by
  set τ := 1 / Real.cosh v with hτ
  set t := Real.tanh v with ht
  have hc := Real.cosh_pos v
  have hc1 := Real.one_lt_cosh.mpr hv.ne'
  have hτ0 : 0 < τ := by positivity
  have hτ1 : τ < 1 := by rw [hτ, div_lt_one hc]; exact hc1
  have ht0 : 0 < t := CenteredSupport.tanh_pos hv
  have ht2 : t ^ 2 = 1 - τ ^ 2 := by rw [ht, hτ, ← one_sub_sech_sq]
  have htv : v * τ ≤ t := by
    rw [ht, hτ, Real.tanh_eq_sinh_div_cosh, mul_one_div]
    exact div_le_div_of_nonneg_right (Real.self_le_sinh_iff.mpr hv.le) hc.le
  have hsl : 3 * τ / (2 + τ) ≤ s v := by
    have h := ChannelBounds.s_lower hv
    have e : 3 / (2 * Real.cosh v + 1) = 3 * τ / (2 + τ) := by
      rw [hτ]; field_simp
    rwa [e] at h
  set X := s v - τ ^ 2 with hX
  have hX0 : τ * (1 - τ) * (3 + τ) / (2 + τ) ≤ X := by
    have e : 3 * τ / (2 + τ) - τ ^ 2 = τ * (1 - τ) * (3 + τ) / (2 + τ) := by
      field_simp; ring
    linarith
  have hsd : sd v = -X / t := by unfold sd; rw [hX]; ring
  have hA : v * (1 + τ + τ ^ 2) ≤ v * (1 + τ ^ 2) + t := by nlinarith
  have hX0n : 0 ≤ τ * (1 - τ) * (3 + τ) / (2 + τ) := by
    apply div_nonneg _ (by linarith); apply mul_nonneg (mul_nonneg hτ0.le (by linarith)); linarith
  have hXA : τ * (1 - τ) * (3 + τ) / (2 + τ) * (v * (1 + τ + τ ^ 2)) ≤
      X * (v * (1 + τ ^ 2) + t) :=
    mul_le_mul hX0 hA (by positivity) (le_trans hX0n hX0)
  have hpoly : τ * (1 - τ) * (3 + τ) / (2 + τ) * (v * (1 + τ + τ ^ 2)) -
      2 * v * τ ^ 2 * (1 - τ ^ 2) = v * τ * (1 - τ) * (3 - 2 * τ ^ 2 - τ ^ 3) / (2 + τ) := by
    field_simp; ring
  have hpos : 0 ≤ v * τ * (1 - τ) * (3 - 2 * τ ^ 2 - τ ^ 3) / (2 + τ) := by
    apply div_nonneg _ (by linarith)
    apply mul_nonneg (mul_nonneg (mul_nonneg hv.le hτ0.le) (by linarith))
    nlinarith
  have hN : 0 ≤ X * (v * (1 + τ ^ 2) + t) - 2 * v * τ ^ 2 * t ^ 2 := by
    rw [ht2]; linarith
  have e : v * sdd v - sd v = (X * (v * (1 + τ ^ 2) + t) - 2 * v * τ ^ 2 * t ^ 2) / t ^ 2 := by
    unfold sdd
    rw [← hτ, ← ht, hsd]
    field_simp
    ring
  have := div_nonneg hN (sq_nonneg t)
  linarith

/-- Monotone on `(0,∞)` with limit `0` at `0⁺` implies nonnegative. -/
theorem nonneg_of_monotoneOn_tendsto {g : ℝ → ℝ} (hm : MonotoneOn g (Ioi 0))
    (ht : Tendsto g (𝓝[>] 0) (𝓝 0)) {v : ℝ} (hv : 0 < v) : 0 ≤ g v := by
  apply le_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsGT hv] with u hu
  exact hm hu.1 hv hu.2.le

theorem tendsto_one_sub_s : Tendsto (fun v => 1 - s v) (𝓝[>] 0) (𝓝 0) := by
  have hl : Tendsto (fun v => 1 - 3 / (2 * Real.cosh v + 1)) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (fun v => 1 - 3 / (2 * Real.cosh v + 1)) := by
      apply Continuous.sub continuous_const
      apply Continuous.div continuous_const (by fun_prop)
      intro x; have := Real.cosh_pos x; linarith
    have := hcont.continuousAt (x := 0) |>.tendsto
    simp only [Real.cosh_zero] at this
    norm_num at this
    exact this.mono_left nhdsWithin_le_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hl
  · filter_upwards [self_mem_nhdsWithin] with v hv
    exact sub_nonneg.mpr (s_lt_one hv).le
  · filter_upwards [self_mem_nhdsWithin] with v hv
    linarith [ChannelBounds.s_lower (show 0 < v from hv)]

theorem tendsto_v_tanh : Tendsto (fun v => v * Real.tanh v) (𝓝[>] 0) (𝓝 0) := by
  have hcont : Continuous (fun v => v * Real.tanh v) := continuous_id.mul continuous_tanh
  have := hcont.continuousAt (x := 0) |>.tendsto
  simp only [Real.tanh_zero, mul_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- `f' = -s'` satisfies `0 < f' ≤ tanh v`. -/
theorem neg_sd_le_tanh {v : ℝ} (hv : 0 < v) : -sd v ≤ Real.tanh v := by
  have ht0 := CenteredSupport.tanh_pos hv
  have hs1 := s_lt_one hv
  have e : -sd v = (s v - (1 / Real.cosh v) ^ 2) / Real.tanh v := by unfold sd; ring
  rw [e, div_le_iff₀ ht0]
  have := one_sub_sech_sq v
  nlinarith

/-- `m = 2f - v f' ≥ 0`, with `f = 1 - s`. -/
theorem two_f_ge {v : ℝ} (hv : 0 < v) : v * (-sd v) ≤ 2 * (1 - s v) := by
  let m : ℝ → ℝ := fun u => 2 * (1 - s u) - u * (-sd u)
  have hmd : ∀ u, 0 < u → HasDerivAt m (-sd u + u * sdd u) u := by
    intro u hu
    have := (((hasDerivAt_s hu).const_sub 1).const_mul 2).sub
      ((hasDerivAt_id' u).mul (hasDerivAt_sd hu).neg)
    refine this.congr_deriv ?_
    simp only [Pi.neg_apply]
    ring
  have hmono : MonotoneOn m (Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · intro u hu; exact (hmd u hu).continuousAt.continuousWithinAt
    · rw [interior_Ioi]; intro u hu; exact (hmd u hu).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]; intro u hu
      rw [(hmd u hu).deriv]
      linarith [sd_le_v_sdd hu]
  have hlim : Tendsto m (𝓝[>] 0) (𝓝 0) := by
    have h2 : Tendsto (fun u => u * (-sd u)) (𝓝[>] 0) (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_v_tanh
      · filter_upwards [self_mem_nhdsWithin] with u hu
        exact mul_nonneg (le_of_lt hu) (neg_nonneg.mpr (sd_neg hu).le)
      · filter_upwards [self_mem_nhdsWithin] with u hu
        exact mul_le_mul_of_nonneg_left (neg_sd_le_tanh hu) (le_of_lt hu)
    have := (tendsto_one_sub_s.const_mul 2).sub h2
    show Tendsto (fun u => 2 * (1 - s u) - u * (-sd u)) _ _
    simpa using this
  have := nonneg_of_monotoneOn_tendsto hmono hlim hv
  simp only [m] at this
  linarith

theorem hasDerivAt_k {v : ℝ} (hv : 0 < v) :
    HasDerivAt k (2 * sd v ^ 2 - 2 * (1 - s v) * sdd v) v := by
  have := ((((hasDerivAt_s hv).const_sub 1).const_mul 2).mul (hasDerivAt_sd hv)).neg
  refine this.congr_deriv ?_
  ring

/-- Manuscript (angle-curvature-scaling): `c - v c' ≥ v² k / 5` for `v > 0`. -/
theorem angle_curvature_scaling {v : ℝ} (hv : 0 < v) :
    v ^ 2 / 5 * k v ≤ c v - v * cd v := by
  let Ψ : ℝ → ℝ := fun u => c u - u * cd u - u ^ 2 / 5 * k u
  have hΨd : ∀ u, 0 < u → HasDerivAt Ψ
      (cd u - (cd u + u * (2 * (1 - s u) * sd u)) -
        (2 * u / 5 * k u + u ^ 2 / 5 * (2 * sd u ^ 2 - 2 * (1 - s u) * sdd u))) u := by
    intro u hu
    have h1 := (hasDerivAt_c hu).sub ((hasDerivAt_id' u).mul (hasDerivAt_cd hu))
    have h2 := (((hasDerivAt_id' u).pow 2).div_const 5).mul (hasDerivAt_k hu)
    refine (h1.sub h2).congr_deriv ?_
    simp only [Pi.pow_apply]
    push_cast
    ring
  have hmono : MonotoneOn Ψ (Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · intro u hu; exact (hΨd u hu).continuousAt.continuousWithinAt
    · rw [interior_Ioi]; intro u hu; exact (hΨd u hu).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]; intro u hu
      have hu' : 0 < u := hu
      rw [(hΨd u hu).deriv]
      have hf0 : 0 ≤ 1 - s u := sub_nonneg.mpr (s_lt_one hu).le
      have hf1 : 0 ≤ -sd u := neg_nonneg.mpr (sd_neg hu).le
      have hi := sd_le_v_sdd hu
      have hii := two_f_ge hu
      -- derivative = (2u/5) [f(3f' - u f'') - u f'²] with f = 1-s, f' = -sd, f'' = -sdd
      have e : cd u - (cd u + u * (2 * (1 - s u) * sd u)) -
          (2 * u / 5 * k u + u ^ 2 / 5 * (2 * sd u ^ 2 - 2 * (1 - s u) * sdd u)) =
          2 * u / 5 * ((1 - s u) * (3 * (-sd u) - u * (-sdd u)) - u * (-sd u) ^ 2) := by
        unfold k; ring
      rw [e]
      apply mul_nonneg (by positivity)
      have h3 : 2 * (-sd u) ≤ 3 * (-sd u) - u * (-sdd u) := by linarith
      have h4 : (1 - s u) * (2 * (-sd u)) ≤ (1 - s u) * (3 * (-sd u) - u * (-sdd u)) :=
        mul_le_mul_of_nonneg_left h3 hf0
      have h5 : u * (-sd u) * (-sd u) ≤ 2 * (1 - s u) * (-sd u) :=
        mul_le_mul_of_nonneg_right hii hf1
      nlinarith
  have hlim : Tendsto Ψ (𝓝[>] 0) (𝓝 0) := by
    have hc0 : Tendsto c (𝓝[>] 0) (𝓝 0) := by
      have := continuousAt_c_zero.tendsto
      rw [c_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hid : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto (0:ℝ))
    have hcd : Tendsto (fun u => u * cd u) (𝓝[>] 0) (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hid
      · filter_upwards [self_mem_nhdsWithin] with u hu
        exact mul_nonneg (le_of_lt hu) (cd_pos hu).le
      · filter_upwards [self_mem_nhdsWithin] with u hu
        have h1 : cd u ≤ 1 := by have := one_sub_cd u; nlinarith [sq_nonneg (1 - s u)]
        nlinarith [show (0:ℝ) < u from hu]
    have hk : Tendsto (fun u => u ^ 2 / 5 * k u) (𝓝[>] 0) (𝓝 0) := by
      have hsq : Tendsto (fun u : ℝ => u ^ 2 / 10) (𝓝[>] 0) (𝓝 0) := by
        have := (hid.pow 2).div_const 10
        simpa using this
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsq
      · filter_upwards [self_mem_nhdsWithin] with u hu
        exact mul_nonneg (by positivity) (k_pos hu).le
      · filter_upwards [self_mem_nhdsWithin] with u hu
        have := k_lt_half (show 0 < u from hu)
        nlinarith [sq_nonneg u]
    have := (hc0.sub hcd).sub hk
    simpa using this
  have := nonneg_of_monotoneOn_tendsto hmono hlim hv
  simp only [Ψ] at this
  linarith

/-! ### Entropy profile calculus: `𝓗 = cosh·h(tanh)`, `Λ = log(2cosh)`, `J = sinh/𝓗 = 1/F` -/

noncomputable def Hc (v : ℝ) : ℝ := Real.cosh v * h (Real.tanh v)
noncomputable def Lam (v : ℝ) : ℝ := Real.log (2 * Real.cosh v)
noncomputable def Hc1 (v : ℝ) : ℝ := Real.sinh v * Lam v - v * Real.cosh v
noncomputable def Hc2 (v : ℝ) : ℝ := Real.cosh v * h (Real.tanh v) - 1 / Real.cosh v
noncomputable def Jf (v : ℝ) : ℝ := Real.sinh v / Hc v
noncomputable def J1f (v : ℝ) : ℝ := Lam v / Hc v ^ 2
noncomputable def J2f (v : ℝ) : ℝ := Real.tanh v / Hc v ^ 2 - 2 * Lam v * Hc1 v / Hc v ^ 3
noncomputable def J3f (v : ℝ) : ℝ :=
  (1 / Real.cosh v) ^ 2 / Hc v ^ 2 - 4 * Real.tanh v * Hc1 v / Hc v ^ 3 -
    2 * Lam v * Hc2 v / Hc v ^ 3 + 6 * Lam v * Hc1 v ^ 2 / Hc v ^ 4
noncomputable def Df (v : ℝ) : ℝ := v * J1f v - Jf v

theorem Hc_pos (v : ℝ) : 0 < Hc v := mul_pos (Real.cosh_pos v) (h_tanh_pos v)

theorem Lam_eq (v : ℝ) : Lam v = v + Real.log (1 + ChannelBounds.q v) := by
  unfold Lam ChannelBounds.q
  have e : 2 * Real.cosh v = Real.exp v * (1 + Real.exp (-2 * v)) := by
    rw [Real.cosh_eq, mul_add, mul_one, ← Real.exp_add]
    ring_nf
  rw [e, Real.log_mul (Real.exp_pos v).ne' (by positivity), Real.log_exp]

theorem lam_identity (v : ℝ) : h (Real.tanh v) + v * Real.tanh v = Lam v := by
  rw [ChannelBounds.h_tanh_eq_q, Lam_eq, ChannelBounds.tanh_eq_q]
  have hq := ChannelBounds.q_pos v
  field_simp
  ring

theorem Lam_pos (v : ℝ) : 0 < Lam v := by
  unfold Lam
  apply Real.log_pos
  have := Real.one_le_cosh v
  linarith

theorem hasDerivAt_Lam (v : ℝ) : HasDerivAt Lam (Real.tanh v) v := by
  have hc := (Real.cosh_pos v).ne'
  have := ((Real.hasDerivAt_cosh v).const_mul 2).log (by positivity)
  refine this.congr_deriv ?_
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

theorem Hc_eq (v : ℝ) : Hc v = Real.cosh v * Lam v - v * Real.sinh v := by
  have hc := (Real.cosh_pos v).ne'
  have hh : h (Real.tanh v) = Lam v - v * Real.tanh v := by linarith [lam_identity v]
  unfold Hc
  rw [hh, Real.tanh_eq_sinh_div_cosh]
  field_simp

theorem hasDerivAt_Hc (v : ℝ) : HasDerivAt Hc (Hc1 v) v := by
  have hc := (Real.cosh_pos v).ne'
  have := (Real.hasDerivAt_cosh v).mul (hasDerivAt_h_tanh v)
  refine this.congr_deriv ?_
  have hh : h (Real.tanh v) = Lam v - v * Real.tanh v := by linarith [lam_identity v]
  have e : Real.sinh v * (Lam v - v * Real.tanh v) + Real.cosh v * (-v / Real.cosh v ^ 2) =
      Real.sinh v * Lam v - v * (Real.sinh v ^ 2 + 1) / Real.cosh v := by
    rw [Real.tanh_eq_sinh_div_cosh]; field_simp; ring
  unfold Hc1
  rw [hh, e]
  have hs : Real.sinh v ^ 2 + 1 = Real.cosh v ^ 2 := by linarith [Real.cosh_sq_sub_sinh_sq v]
  rw [hs]
  field_simp

theorem hasDerivAt_Hc1 (v : ℝ) : HasDerivAt Hc1 (Hc2 v) v := by
  have hc := (Real.cosh_pos v).ne'
  have := ((Real.hasDerivAt_sinh v).mul (hasDerivAt_Lam v)).sub
    ((hasDerivAt_id' v).mul (Real.hasDerivAt_cosh v))
  refine this.congr_deriv ?_
  unfold Hc2
  have hl := lam_identity v
  have hh : h (Real.tanh v) = Lam v - v * Real.tanh v := by linarith
  rw [hh, Real.tanh_eq_sinh_div_cosh]
  field_simp
  nlinarith [Real.cosh_sq_sub_sinh_sq v]

theorem hasDerivAt_Jf (v : ℝ) : HasDerivAt Jf (J1f v) v := by
  have hH := (Hc_pos v).ne'
  have := (Real.hasDerivAt_sinh v).div (hasDerivAt_Hc v) hH
  refine this.congr_deriv ?_
  have key : Real.cosh v * Hc v - Real.sinh v * Hc1 v = Lam v := by
    rw [Hc_eq]; unfold Hc1
    linear_combination Lam v * Real.cosh_sq_sub_sinh_sq v
  unfold J1f
  rw [key]

theorem hasDerivAt_J1f (v : ℝ) : HasDerivAt J1f (J2f v) v := by
  have hH := (Hc_pos v).ne'
  have := (hasDerivAt_Lam v).div ((hasDerivAt_Hc v).pow 2) (pow_ne_zero 2 hH)
  refine this.congr_deriv ?_
  unfold J2f
  simp only [Pi.pow_apply]
  field_simp
  push_cast
  ring

theorem hasDerivAt_J2f (v : ℝ) : HasDerivAt J2f (J3f v) v := by
  have hH := (Hc_pos v).ne'
  have hc := (Real.cosh_pos v).ne'
  have t1 := (hasDerivAt_tanh v).div ((hasDerivAt_Hc v).pow 2) (pow_ne_zero 2 hH)
  have t2 := (((hasDerivAt_Lam v).const_mul 2).mul (hasDerivAt_Hc1 v)).div
    ((hasDerivAt_Hc v).pow 3) (pow_ne_zero 3 hH)
  refine (t1.sub t2).congr_deriv ?_
  unfold J3f
  simp only [Pi.pow_apply, Pi.mul_apply]
  field_simp
  push_cast
  ring

theorem hasDerivAt_Df (v : ℝ) : HasDerivAt Df (v * J2f v) v := by
  have := ((hasDerivAt_id' v).mul (hasDerivAt_J1f v)).sub (hasDerivAt_Jf v)
  refine this.congr_deriv ?_
  ring

/-- `𝓗' < 0`, i.e. `tanh v · log(2 cosh v) < v`, for `v > 0`. -/
theorem Hc1_neg {v : ℝ} (hv : 0 < v) : Hc1 v < 0 := by
  have hq0 := ChannelBounds.q_pos v
  have hq1 := ChannelBounds.q_lt_one hv
  have hLq : Real.log (1 + ChannelBounds.q v) ≤ ChannelBounds.q v := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + ChannelBounds.q v)
    linarith
  have hvq : 1 - ChannelBounds.q v < 2 * v := by
    have hh := Real.add_one_lt_exp (by linarith : -2 * v ≠ 0)
    change -2 * v + 1 < ChannelBounds.q v at hh
    linarith
  have hmul : (1 - ChannelBounds.q v) * Real.log (1 + ChannelBounds.q v) <
      2 * v * ChannelBounds.q v := by
    have h1 := mul_le_mul_of_nonneg_left hLq (by linarith : 0 ≤ 1 - ChannelBounds.q v)
    have h2 := mul_lt_mul_of_pos_right hvq hq0
    linarith
  have e : Hc1 v = Real.cosh v * (Real.tanh v * Lam v - v) := by
    unfold Hc1; rw [Real.tanh_eq_sinh_div_cosh]; field_simp
  rw [e]
  apply mul_neg_of_pos_of_neg (Real.cosh_pos v)
  rw [Lam_eq, ChannelBounds.tanh_eq_q]
  rw [div_mul_eq_mul_div, sub_neg, div_lt_iff₀ (by linarith)]
  nlinarith

theorem J2f_pos {v : ℝ} (hv : 0 < v) : 0 < J2f v := by
  have hH := Hc_pos v
  have h1 : 0 < Real.tanh v / Hc v ^ 2 := div_pos (CenteredSupport.tanh_pos hv) (by positivity)
  have h2 : 2 * Lam v * Hc1 v / Hc v ^ 3 < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith [Lam_pos v]) (Hc1_neg hv))
      (by positivity)
  unfold J2f; linarith

theorem Df_zero : Df 0 = 0 := by simp [Df, Jf]

/-- `D = vJ' - J > 0` for `v > 0`. -/
theorem Df_pos {v : ℝ} (hv : 0 < v) : 0 < Df v := by
  have hmono : StrictMonoOn Df (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · intro u _; exact (hasDerivAt_Df u).continuousAt.continuousWithinAt
    · rw [interior_Ici]; intro u hu
      rw [(hasDerivAt_Df u).deriv]
      exact mul_pos hu (J2f_pos hu)
  have := hmono (by simp : (0:ℝ) ∈ Ici 0) hv.le hv
  rwa [Df_zero] at this

theorem Jf_eq_inv_F {v : ℝ} (hv : 0 < v) : Jf v = 1 / F v := by
  have hc := (Real.cosh_pos v).ne'
  have hh := (h_tanh_pos v).ne'
  have ht := (CenteredSupport.tanh_pos hv).ne'
  unfold Jf Hc F
  rw [Real.tanh_eq_sinh_div_cosh] at ht ⊢
  field_simp

/-! ### Entropy curvature, branch `0 < v ≤ 1` -/

theorem exp_two_gt_seven : (7:ℝ) < Real.exp 2 := by
  have h := (ChannelBounds.exp_one_bounds).1
  have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]; nlinarith

theorem q_one_lt : ChannelBounds.q 1 < 1/7 := by
  unfold ChannelBounds.q
  rw [show -2 * (1:ℝ) = -2 by ring, Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 2) (by norm_num)]
  norm_num
  exact exp_two_gt_seven

theorem cosh_sq_q (v : ℝ) : 4 * ChannelBounds.q v * Real.cosh v ^ 2 = (1 + ChannelBounds.q v) ^ 2 := by
  unfold ChannelBounds.q
  rw [show -2 * v = -(v + v) by ring, Real.exp_neg, Real.exp_add, Real.cosh_eq, Real.exp_neg]
  have he := (Real.exp_pos v).ne'
  field_simp
  ring

theorem sech_sq_q (v : ℝ) :
    (1 / Real.cosh v) ^ 2 = 4 * ChannelBounds.q v / (1 + ChannelBounds.q v) ^ 2 := by
  have hc := (Real.cosh_pos v).ne'
  have hq := ChannelBounds.q_pos v
  rw [← cosh_sq_q]
  field_simp

/-- `h(tanh v) < sech² v` on `(0,1]`, i.e. `𝓗'' < 0` there. -/
theorem h_tanh_lt_sech_sq {v : ℝ} (hv0 : 0 < v) (hv1 : v ≤ 1) :
    h (Real.tanh v) < (1 / Real.cosh v) ^ 2 := by
  let ψ : ℝ → ℝ := fun u => (1 / Real.cosh u) ^ 2 - h (Real.tanh u)
  have hψd : ∀ u, HasDerivAt ψ ((1 / Real.cosh u) ^ 2 * (u - 2 * Real.tanh u)) u := by
    intro u
    have := (hasDerivAt_sech_sq u).sub (hasDerivAt_h_tanh u)
    refine this.congr_deriv ?_
    have hc := (Real.cosh_pos u).ne'
    field_simp
    ring
  have hanti : AntitoneOn ψ (Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · intro u _; exact (hψd u).continuousAt.continuousWithinAt
    · intro u _; exact (hψd u).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro u hu
      rw [(hψd u).deriv]
      apply mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
      have hc := Real.cosh_pos u
      have hcs := ChannelBounds.cosh_small ⟨hu.1.le, hu.2.le⟩
      have hs := Real.self_le_sinh_iff.mpr hu.1.le
      have ht : u / (1 + 3 * u ^ 2 / 5) ≤ Real.tanh u := by
        rw [Real.tanh_eq_sinh_div_cosh]
        calc u / (1 + 3 * u ^ 2 / 5) ≤ u / Real.cosh u :=
              div_le_div_of_nonneg_left hu.1.le hc hcs
          _ ≤ Real.sinh u / Real.cosh u := div_le_div_of_nonneg_right hs hc.le
      have hd : 0 < 1 + 3 * u ^ 2 / 5 := by positivity
      rw [div_le_iff₀ hd] at ht
      have h2 : u ^ 2 ≤ 1 := by nlinarith [hu.1, hu.2]
      have htp := CenteredSupport.tanh_pos hu.1
      nlinarith [hu.1]
  have hψ1 : 0 < ψ 1 := by
    have hq0 := ChannelBounds.q_pos 1
    have hq1 := q_one_lt
    have hL : Real.log (1 + ChannelBounds.q 1) ≤ ChannelBounds.q 1 := by
      have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + ChannelBounds.q 1)
      linarith
    simp only [ψ]
    rw [sech_sq_q, ChannelBounds.h_tanh_eq_q]
    have key : ChannelBounds.q 1 + 2 * 1 * ChannelBounds.q 1 / (1 + ChannelBounds.q 1) <
        4 * ChannelBounds.q 1 / (1 + ChannelBounds.q 1) ^ 2 := by
      have e : ChannelBounds.q 1 + 2 * 1 * ChannelBounds.q 1 / (1 + ChannelBounds.q 1) =
          ChannelBounds.q 1 * (3 + ChannelBounds.q 1) / (1 + ChannelBounds.q 1) := by
        field_simp; ring
      rw [e, div_lt_div_iff₀ (by positivity) (by positivity)]
      have hq2 : 0 < ChannelBounds.q 1 * (1 + ChannelBounds.q 1) := by positivity
      nlinarith [mul_pos hq2 hq0]
    linarith
  have := hanti ⟨hv0.le, hv1⟩ ⟨zero_le_one, le_rfl⟩ hv1
  simp only [ψ] at this hψ1
  linarith

theorem Hc2_neg {v : ℝ} (hv0 : 0 < v) (hv1 : v ≤ 1) : Hc2 v < 0 := by
  have hc := Real.cosh_pos v
  have hlt := h_tanh_lt_sech_sq hv0 hv1
  have e : Hc2 v = Real.cosh v * (h (Real.tanh v) - (1 / Real.cosh v) ^ 2) := by
    unfold Hc2; field_simp
  rw [e]
  exact mul_neg_of_pos_of_neg hc (by linarith)

theorem J3f_pos {v : ℝ} (hv0 : 0 < v) (hv1 : v ≤ 1) : 0 < J3f v := by
  have hH := Hc_pos v
  have hL := Lam_pos v
  have h1 := Hc1_neg hv0
  have h2 := Hc2_neg hv0 hv1
  have ht := CenteredSupport.tanh_pos hv0
  have a : 0 < (1 / Real.cosh v) ^ 2 / Hc v ^ 2 := by
    have := Real.cosh_pos v; positivity
  have b : 0 < -(4 * Real.tanh v * Hc1 v / Hc v ^ 3) := by
    rw [← neg_div]; apply div_pos _ (by positivity); nlinarith
  have c' : 0 < -(2 * Lam v * Hc2 v / Hc v ^ 3) := by
    rw [← neg_div]; apply div_pos _ (by positivity); nlinarith
  have d : 0 ≤ 6 * Lam v * Hc1 v ^ 2 / Hc v ^ 4 := by positivity
  unfold J3f; linarith

/-- Manuscript (original-profile-curvature): `2D < v² J''` for `0 < v ≤ 1`. -/
theorem profile_curvature_small {v : ℝ} (hv0 : 0 < v) (hv1 : v ≤ 1) :
    2 * Df v < v ^ 2 * J2f v := by
  let E : ℝ → ℝ := fun u => u ^ 2 / 2 * J2f u - Df u
  have hEd : ∀ u, HasDerivAt E (u ^ 2 / 2 * J3f u) u := by
    intro u
    have := ((((hasDerivAt_id' u).pow 2).div_const 2).mul (hasDerivAt_J2f u)).sub (hasDerivAt_Df u)
    refine this.congr_deriv ?_
    simp only [Pi.pow_apply]
    push_cast
    ring
  have hmono : StrictMonoOn E (Icc 0 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
    · intro u _; exact (hEd u).continuousAt.continuousWithinAt
    · rw [interior_Icc]; intro u hu
      rw [(hEd u).deriv]
      exact mul_pos (by have := hu.1; positivity) (J3f_pos hu.1 hu.2.le)
  have h0 : E 0 = 0 := by simp [E, Df_zero]
  have := hmono ⟨le_rfl, zero_le_one⟩ ⟨hv0.le, hv1⟩ hv0
  rw [h0] at this
  simp only [E] at this
  linarith

/-! ### Entropy curvature, branch `v ≥ 1` (q-form, manuscript `(qD)' > 0`) -/

/-- `P = qK³(vJ'' - 2D)` in the variables `v`, `q = e^{-2v}`, `T = log(1+q)/q`,
with `K = 2v + (1+q)T` and `T' = 2(T - 1/(1+q))`. -/
noncomputable def Pq (v q T : ℝ) : ℝ :=
  (2*v + (1+q)*T) * (2*T*(1-q+2*T) - (2*v + (1+q)*T) * (2*q + 2*(2*(T - 1/(1+q))))) +
  (2*v + (1+q)*T) * (4*q^2*T^2 + 2*(1-q^2)*T*(2*(T - 1/(1+q)))) - 4*(1-q^2)*T^3

set_option maxHeartbeats 4000000 in
theorem qform_algebra (v E L S C tv hh Lm q : ℝ) (hE : 0 < E) (hL : 0 < L) (hv : 0 < v)
    (hq : q = 1 / E ^ 2) (hS : S = (E - 1/E)/2) (hC : C = (E + 1/E)/2) (ht : tv = S / C)
    (hhh : hh = L + 2*v*q/(1+q)) (hLm : Lm = v + L) :
    q * (2*v + (1+q)*(L/q)) ^ 3 *
      (v * (tv / (C*hh)^2 - 2*Lm*(S*Lm - v*C)/(C*hh)^3) -
        2 * (v * (Lm/(C*hh)^2) - S/(C*hh))) = Pq v q (L/q) := by
  subst hq hS hC ht hhh hLm
  have hE' : E ≠ 0 := hE.ne'
  have hC0 : 0 < (E + 1/E)/2 := by positivity
  have hh0 : 0 < L + 2*v*(1/E^2)/(1+1/E^2) := by positivity
  have hK : 0 < 2*v + (1+1/E^2)*(L/(1/E^2)) := by positivity
  unfold Pq
  field_simp
  ring

theorem q_eq_inv (v : ℝ) : ChannelBounds.q v = 1 / Real.exp v ^ 2 := by
  unfold ChannelBounds.q
  rw [show -2 * v = -(2 * v) by ring, Real.exp_neg, ← Real.exp_nat_mul]
  norm_num

theorem qform_actual {v : ℝ} (hv : 0 < v) :
    ChannelBounds.q v * (2*v + (1 + ChannelBounds.q v) *
      (Real.log (1 + ChannelBounds.q v) / ChannelBounds.q v)) ^ 3 * (v * J2f v - 2 * Df v) =
    Pq v (ChannelBounds.q v) (Real.log (1 + ChannelBounds.q v) / ChannelBounds.q v) := by
  have hL : 0 < Real.log (1 + ChannelBounds.q v) :=
    Real.log_pos (by linarith [ChannelBounds.q_pos v])
  have hS : Real.sinh v = (Real.exp v - 1 / Real.exp v) / 2 := by
    rw [Real.sinh_eq, Real.exp_neg, one_div]
  have hC : Real.cosh v = (Real.exp v + 1 / Real.exp v) / 2 := by
    rw [Real.cosh_eq, Real.exp_neg, one_div]
  have hh : h (Real.tanh v) = Real.log (1 + ChannelBounds.q v) +
      2 * v * ChannelBounds.q v / (1 + ChannelBounds.q v) := ChannelBounds.h_tanh_eq_q v
  have := qform_algebra v (Real.exp v) (Real.log (1 + ChannelBounds.q v)) (Real.sinh v)
    (Real.cosh v) (Real.tanh v) (h (Real.tanh v)) (Lam v) (ChannelBounds.q v) (Real.exp_pos v) hL hv
    (q_eq_inv v) hS hC (Real.tanh_eq_sinh_div_cosh v) hh (Lam_eq v)
  rw [← this]
  unfold J2f Df J1f Jf Hc Hc1
  rfl

theorem log_one_add_lower {x : ℝ} (hx : 0 ≤ x) : x - x^2/2 ≤ Real.log (1 + x) := by
  let g : ℝ → ℝ := fun y => Real.log (1 + y) - y + y^2/2
  have hgd : ∀ y, 0 ≤ y → HasDerivAt g (1/(1+y) - 1 + y) y := by
    intro y hy
    have := (((hasDerivAt_id' y).const_add 1).log (by linarith)).sub (hasDerivAt_id' y)
      |>.add (((hasDerivAt_id' y).pow 2).div_const 2)
    refine this.congr_deriv ?_
    have : (1:ℝ) + y ≠ 0 := by linarith
    field_simp
    ring
  have hm : MonotoneOn g (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro y hy; exact (hgd y hy).continuousAt.continuousWithinAt
    · rw [interior_Ici]; intro y hy; exact (hgd y hy.le).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]; intro y hy
      have hy' : 0 < y := hy
      rw [(hgd y hy'.le).deriv]
      have e : 1/(1+y) - 1 + y = y^2/(1+y) := by field_simp; ring
      rw [e]; positivity
  have := hm (by simp : (0:ℝ) ∈ Ici 0) hx hx
  simp only [g] at this
  norm_num at this
  linarith

theorem log_one_add_trapezoid {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ x * (2 + x) / (2 * (1 + x)) := by
  let g : ℝ → ℝ := fun y => y * (2 + y) / (2 * (1 + y)) - Real.log (1 + y)
  have hgd : ∀ y, 0 ≤ y → HasDerivAt g (y^2 / (2 * (1 + y)^2)) y := by
    intro y hy
    have h1 : (2:ℝ) * (1 + y) ≠ 0 := by positivity
    have := (((hasDerivAt_id' y).mul ((hasDerivAt_id' y).const_add 2)).div
      (((hasDerivAt_id' y).const_add 1).const_mul 2) h1).sub
      (((hasDerivAt_id' y).const_add 1).log (by linarith))
    refine this.congr_deriv ?_
    simp only [Pi.mul_apply]
    field_simp; ring
  have hm : MonotoneOn g (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro y hy; exact (hgd y hy).continuousAt.continuousWithinAt
    · rw [interior_Ici]; intro y hy; exact (hgd y hy.le).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]; intro y hy
      rw [(hgd y (le_of_lt hy)).deriv]; positivity
  have := hm (by simp : (0:ℝ) ∈ Ici 0) hx hx
  simp only [g] at this
  norm_num at this
  linarith

theorem log_one_add_gt {x : ℝ} (hx : 0 < x) : x / (1 + x) < Real.log (1 + x) := by
  have h := Real.log_lt_sub_one_of_pos (by positivity : 0 < 1 / (1 + x))
    (by rw [ne_eq, div_eq_one_iff_eq (by positivity)]; linarith)
  rw [one_div, Real.log_inv] at h
  have e : (1 + x)⁻¹ - 1 = -(x / (1 + x)) := by field_simp; ring
  linarith

theorem log_one_add_lt {x : ℝ} (hx : 0 < x) : Real.log (1 + x) < x := by
  have := Real.log_lt_sub_one_of_pos (by linarith : 0 < 1 + x) (by linarith)
  linarith

theorem Pq_pos {v q T : ℝ} (hv : 1 ≤ v) (hq0 : 0 < q) (hq1 : q < 1/7)
    (hT1 : 1 - q/2 ≤ T) (hT2 : T < 1) (hT3 : 1/(1+q) < T) (hT4 : T ≤ (2+q)/(2*(1+q)))
    (hqK : q * (2*v + (1+q)*T) < 1/2) : 0 < Pq v q T := by
  set K := 2*v + (1+q)*T with hK
  set Tp := 2*(T - 1/(1+q)) with hTp
  have hTpos : 0 < T := by linarith
  have hK2 : 2 < K := by rw [hK]; nlinarith
  have hTp0 : 0 < Tp := by rw [hTp]; linarith
  have hTpq : Tp < q := by
    have e : (2+q)/(2*(1+q)) - 1/(1+q) = q/(2*(1+q)) := by field_simp; ring
    have : q/(2*(1+q)) < q/2 := by
      apply div_lt_div_of_pos_left hq0 (by norm_num); nlinarith
    rw [hTp]; linarith
  have hA1 : 5 < 2*T*(1-q+2*T) := by nlinarith
  have hA2 : K * (2*q + 2*Tp) < 2 := by nlinarith
  have hM : 0 ≤ 4*q^2*T^2 + 2*(1-q^2)*T*Tp := by
    have : 0 ≤ 1 - q^2 := by nlinarith
    positivity
  have hA3 : 4*(1-q^2)*T^3 < 2*K := by
    have hT3' : T^3 < 1 := by
      calc T^3 < 1^3 := by gcongr
        _ = 1 := by norm_num
    nlinarith [sq_nonneg q]
  have e : Pq v q T = K * (2*T*(1-q+2*T) - K*(2*q + 2*Tp)) + K*(4*q^2*T^2 + 2*(1-q^2)*T*Tp)
      - 4*(1-q^2)*T^3 := by unfold Pq; rfl
  rw [e]
  have h1 : K * 3 < K * (2*T*(1-q+2*T) - K*(2*q + 2*Tp)) :=
    mul_lt_mul_of_pos_left (by linarith) (by linarith)
  have h2 : 0 ≤ K*(4*q^2*T^2 + 2*(1-q^2)*T*Tp) := mul_nonneg (by linarith) hM
  linarith

theorem q_le_q_one {v : ℝ} (hv : 1 ≤ v) : ChannelBounds.q v ≤ ChannelBounds.q 1 := by
  unfold ChannelBounds.q; apply Real.exp_le_exp.mpr; linarith

theorem qK_lt_half {v : ℝ} (hv : 1 ≤ v) :
    ChannelBounds.q v * (2*v + (1 + ChannelBounds.q v) *
      (Real.log (1 + ChannelBounds.q v) / ChannelBounds.q v)) < 1/2 := by
  have hq0 := ChannelBounds.q_pos v
  have hq1 : ChannelBounds.q v < 1/7 := lt_of_le_of_lt (q_le_q_one hv) q_one_lt
  have hL := log_one_add_lt hq0
  have e : ChannelBounds.q v * (2*v + (1 + ChannelBounds.q v) *
      (Real.log (1 + ChannelBounds.q v) / ChannelBounds.q v)) =
      2*v*ChannelBounds.q v + (1 + ChannelBounds.q v) * Real.log (1 + ChannelBounds.q v) := by
    field_simp
  rw [e]
  -- q (2v + 8/7) < 1/2 via e^{2v} ≥ e²(2v - 1) > 7(2v - 1)
  have hX : Real.exp 2 * (2*v - 1) ≤ Real.exp (2*v) := by
    have h1 := Real.add_one_le_exp (2*v - 2)
    have e2 : Real.exp (2*v) = Real.exp 2 * Real.exp (2*v - 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [e2]
    apply mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos 2).le
  have hqX : ChannelBounds.q v * Real.exp (2*v) = 1 := by
    unfold ChannelBounds.q; rw [← Real.exp_add]; norm_num
  have h7 := exp_two_gt_seven
  have hbig : 2 * (2*v + 8/7) < Real.exp (2*v) := by nlinarith
  have hsmall : ChannelBounds.q v * (2*v + 8/7) < 1/2 := by
    have hXpos := Real.exp_pos (2*v)
    nlinarith
  nlinarith

/-- `2D < vJ''` for `v ≥ 1`. -/
theorem profile_curvature_large {v : ℝ} (hv : 1 ≤ v) : 2 * Df v < v * J2f v := by
  have hv0 : 0 < v := by linarith
  have hq0 := ChannelBounds.q_pos v
  have hq1 : ChannelBounds.q v < 1/7 := lt_of_le_of_lt (q_le_q_one hv) q_one_lt
  set L := Real.log (1 + ChannelBounds.q v)
  set T := L / ChannelBounds.q v with hT
  have hT1 : 1 - ChannelBounds.q v / 2 ≤ T := by
    rw [hT, le_div_iff₀ hq0]; have := log_one_add_lower hq0.le; nlinarith
  have hT2 : T < 1 := by rw [hT, div_lt_one hq0]; exact log_one_add_lt hq0
  have hT3 : 1 / (1 + ChannelBounds.q v) < T := by
    rw [hT, lt_div_iff₀ hq0]; have := log_one_add_gt hq0
    have e : 1 / (1 + ChannelBounds.q v) * ChannelBounds.q v =
      ChannelBounds.q v / (1 + ChannelBounds.q v) := by ring
    linarith
  have hT4 : T ≤ (2 + ChannelBounds.q v) / (2 * (1 + ChannelBounds.q v)) := by
    rw [hT, div_le_iff₀ hq0]; have := log_one_add_trapezoid hq0.le
    have e : (2 + ChannelBounds.q v) / (2 * (1 + ChannelBounds.q v)) * ChannelBounds.q v =
      ChannelBounds.q v * (2 + ChannelBounds.q v) / (2 * (1 + ChannelBounds.q v)) := by ring
    linarith
  have hP := Pq_pos hv hq0 hq1 hT1 hT2 hT3 hT4 (qK_lt_half hv)
  have hid := qform_actual hv0
  rw [← hid] at hP
  have hK : 0 < 2*v + (1 + ChannelBounds.q v) * T := by
    have : 0 < T := by linarith
    positivity
  have hpre : 0 < ChannelBounds.q v * (2*v + (1 + ChannelBounds.q v) * T) ^ 3 := by positivity
  have := (pos_iff_pos_of_mul_pos hP).mp hpre
  linarith

/-- Manuscript (profile-ratio-linear): `D/J'' < v/2` for all `v > 0`. -/
theorem profile_ratio_linear {v : ℝ} (hv : 0 < v) : Df v / J2f v < v / 2 := by
  have hJ := J2f_pos hv
  rw [div_lt_iff₀ hJ]
  rcases le_total v 1 with h1 | h1
  · have := profile_curvature_small hv h1
    have : v ^ 2 * J2f v ≤ v * J2f v := by
      have : v ^ 2 ≤ v := by nlinarith
      exact mul_le_mul_of_nonneg_right this hJ.le
    linarith
  · have := profile_curvature_large h1
    linarith

/-! ### The original-yield shape bound and endpoint principle for the actual profiles -/

/-- Manuscript (original-shape): `-c''(vJ' - J)/J'' - (c - vc') < 5/32` for all `v > 0`. -/
theorem original_shape {v : ℝ} (hv : 0 < v) :
    -(2 * (1 - s v) * sd v) * (v * J1f v - Jf v) / J2f v - (c v - v * cd v) < 5/32 := by
  have e : -(2 * (1 - s v) * sd v) * (v * J1f v - Jf v) / J2f v = k v * (Df v / J2f v) := by
    unfold k Df; ring
  rw [e]
  exact shape_of_bounds (k_pos hv) (k_lt_half hv) (profile_ratio_linear hv)
    (angle_curvature_scaling hv)

/-- Endpoint principle for the original yield `Y_P(v) = [r c(v) + A₀ + A₁ J(v)]/v`, `J = 1/F`:
for `r > 0` and `A₀/r ≥ 5/32`, `Y_P` has no interior maximum on `(0,∞)`. -/
theorem original_yield_no_interior_max {r A0 A1 : ℝ} (hr : 0 < r) (hA : 5/32 ≤ A0 / r)
    {a x b : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) :
    (r * c x + A0 + A1 * (1 / F x)) / x ≤
      max ((r * c a + A0 + A1 * (1 / F a)) / a) ((r * c b + A0 + A1 * (1 / F b)) / b) := by
  have hx : 0 < x := by linarith
  have hb : 0 < b := by linarith
  rw [← Jf_eq_inv_F ha, ← Jf_eq_inv_F hx, ← Jf_eq_inv_F hb]
  exact endpoint_principle (c2 := fun v => 2 * (1 - s v) * sd v) hr
    (fun v _ => hasDerivAt_Jf v) (fun v _ => hasDerivAt_J1f v)
    (fun v hv => hasDerivAt_c hv) (fun v hv => hasDerivAt_cd hv)
    (fun v hv => Df_pos hv) (fun v hv => J2f_pos hv)
    (fun v hv => lt_of_lt_of_le (original_shape hv) hA) ha hax hxb

end MostInformativeBit.OriginalYield
