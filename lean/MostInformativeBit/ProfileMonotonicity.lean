import MostInformativeBit.ChannelBounds

/-! scalar.tex Lemma `lem:global-profile`: `v F(v)` strictly decreases on `v > 0`,
and its consequence `a/v ≤ F(ell)/(z F(z))` for `a = F(ell)/F(v)`, `0 < v ≤ z`. -/
namespace MostInformativeBit.ProfileMonotonicity
open Set ChannelProfiles

lemma tanh_lt_self {v : ℝ} (hv : 0 < v) : Real.tanh v < v :=
  lt_trans (tanh_lt_theta hv) (theta_lt_self hv)

lemma hasDerivAt_vF {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun v => v*F v) (F v + v*deriv F v) v := by
  have hh := (hasDerivAt_id' v).mul (hasDerivAt_F hv).differentiableAt.hasDerivAt
  refine hh.congr_deriv ?_
  ring

/-- `(vF)' = F + v F' < 0`, from `-F'/F > coth v > 1/v` (`ChannelBounds.rate_gt_coth`). -/
lemma deriv_vF_neg {v : ℝ} (hv : 0 < v) : F v + v*deriv F v < 0 := by
  have hr := ChannelBounds.rate_gt_coth hv
  unfold ChannelBounds.rate at hr
  have hF := F_pos hv
  have ht := tanh_lt_self hv
  have ht0 := CenteredSupport.tanh_pos hv
  have h1 : 1/v < 1/Real.tanh v := one_div_lt_one_div_of_lt ht0 ht
  have h2 : 1/v < -deriv F v/F v := lt_trans h1 hr
  rw [div_lt_iff₀ hv, div_mul_eq_mul_div, lt_div_iff₀ hF] at h2
  linarith

/-- **Lemma `lem:global-profile`.** `v F(v)` strictly decreases for `v > 0`. -/
theorem vF_strictAntiOn : StrictAntiOn (fun v => v*F v) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro v hv
    exact (hasDerivAt_vF hv).continuousAt.continuousWithinAt
  · intro v hv
    rw [interior_Ioi] at hv
    rw [(hasDerivAt_vF hv).deriv]
    exact deriv_vF_neg hv

/-- The consequence used for (S5): for `0 < v ≤ z` and `a = F(ell)/F(v)`,
`a/v ≤ F(ell)/(z F(z))`. (Needs `ell > 0` only for `F ell > 0`.) -/
theorem pivotal_ratio_le {ell v z : ℝ} (hell : 0 < ell) (hv : 0 < v) (hvz : v ≤ z) :
    (F ell/F v)/v ≤ F ell/(z*F z) := by
  have hz : 0 < z := lt_of_lt_of_le hv hvz
  have hm : z*F z ≤ v*F v := vF_strictAntiOn.antitoneOn hv hz hvz
  rw [div_div, mul_comm (F v) v]
  exact div_le_div_of_nonneg_left (F_pos hell).le (mul_pos hz (F_pos hz)) hm

end MostInformativeBit.ProfileMonotonicity
