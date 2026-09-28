import MostInformativeBit.LowDefinitions

/-! Continuous calculus of `source/low.tex`, subsection "Positivity of the Remaining Gap".

REDUCTION STATUS. Every theorem below that takes `F : LowFixedFacts` is a reduction to the
finite numerical comparisons listed in that record (coordinator's certificate). All derivative,
monotonicity and shape steps are proved here for the actual functions.

* `lowGap_hasDerivAt`, `lowGapFirst_hasDerivAt`, `lowGapSecond_hasDerivAt`,
  `lowGapThird_hasDerivAt`: the proposed derivative chain is correct on `(-1,1)`, with
  `B0'''' = 2[α(1+3r²) - β(r⁴-3r²+6)]/(1-r²)³` (`lowGapFourth`).
* `second_le_max`: `B0''` has no interior maximum on subintervals of `[5/8,1)`.
* `lowGapFirst_neg`, `lowGap_pos`: `B0' < 0` and `B0 > 0` on `[5/8, lowCutoff]`.
* `mean_coefficient_nonneg`: `1/2 - c_ent(r)(1-2r²+r³) ≥ 0` on `[5/8, 1]`.
-/

namespace MostInformativeBit.LowGapCalculus

open MostInformativeBit MostInformativeBit.MeanCorrection MostInformativeBit.TangentMinorant

local notation "α" => lowAlpha
local notation "β" => lowBeta

noncomputable def lowGapFourth (r : ℝ) : ℝ :=
  2 * (α * (1 + 3 * r^2) - β * (r^4 - 3 * r^2 + 6)) / (1 - r^2)^3

/-! ### Derivatives -/

theorem dv2_eq {x : ℝ} (h0 : -1 < x) (h1 : x < 1) : dv2 x = 1 / (1 - x^2) := by
  have hp : (1:ℝ) + x ≠ 0 := by linarith
  have hm : (1:ℝ) - x ≠ 0 := by linarith
  have hq : (1:ℝ) - x^2 ≠ 0 := by nlinarith
  unfold dv2; field_simp; ring

theorem artanh_hasDerivAt {x : ℝ} (h0 : -1 < x) (h1 : x < 1) :
    HasDerivAt Real.artanh (1 / (1 - x^2)) x := by
  rw [← dv2_eq h0 h1]
  apply (dv1_hasDerivAt h0 h1).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds h0 h1] with y hy
  exact artanh_eq_dv1 hy.1 hy.2

theorem h_hasDerivAt' {x : ℝ} (h0 : -1 < x) (h1 : x < 1) :
    HasDerivAt h (-Real.artanh x) x := by
  rw [artanh_eq_dv1 h0 h1]; exact h_hasDerivAt h0 h1

theorem lowGap_hasDerivAt {x : ℝ} (h0 : -1 < x) (h1 : x < 1) :
    HasDerivAt lowGap (lowGapFirst x) x := by
  have hpoly := ((hasDerivAt_id' x).const_sub 1).mul
    (((hasDerivAt_id' x).const_add 1).sub ((hasDerivAt_pow 2 x).const_mul ((49:ℝ)/64)))
  have hw := ((hasDerivAt_pow 2 x).const_mul β).const_sub α
  have hs := hpoly.sub (hw.mul (h_hasDerivAt' h0 h1))
  refine hs.congr_deriv ?_
  simp only [Pi.sub_apply]; unfold lowGapFirst; push_cast; ring

theorem lowGapFirst_hasDerivAt {x : ℝ} (h0 : -1 < x) (h1 : x < 1) :
    HasDerivAt lowGapFirst (lowGapSecond x) x := by
  have hq : (1:ℝ) - x^2 ≠ 0 := by nlinarith
  have t1 := ((hasDerivAt_id' x).const_mul (-2*(1+(49:ℝ)/64)))
  have t2 := (hasDerivAt_pow 2 x).const_mul (3*(49:ℝ)/64)
  have t3 := ((hasDerivAt_id' x).const_mul (2*β)).mul (h_hasDerivAt' h0 h1)
  have t4 := (((hasDerivAt_pow 2 x).const_mul β).const_sub α).mul (artanh_hasDerivAt h0 h1)
  have hs := ((t1.add t2).add t3).add t4
  refine hs.congr_deriv ?_
  unfold lowGapSecond; field_simp; push_cast; ring

theorem lowGapSecond_hasDerivAt {x : ℝ} (h0 : -1 < x) (h1 : x < 1) :
    HasDerivAt lowGapSecond (lowGapThird x) x := by
  have hq : (1:ℝ) - x^2 ≠ 0 := by nlinarith
  have t1 := (hasDerivAt_const x (-2*(1+(49:ℝ)/64)))
  have t2 := (hasDerivAt_id' x).const_mul (6*(49:ℝ)/64)
  have t3 := (h_hasDerivAt' h0 h1).const_mul (2*β)
  have t4 := ((hasDerivAt_id' x).const_mul (4*β)).mul (artanh_hasDerivAt h0 h1)
  have t5 := (((hasDerivAt_pow 2 x).const_mul β).const_sub α).div
    ((hasDerivAt_pow 2 x).const_sub 1) hq
  have hs := (((t1.add t2).add t3).sub t4).add t5
  refine hs.congr_deriv ?_
  unfold lowGapThird; field_simp; push_cast; ring

theorem lowGapThird_hasDerivAt {x : ℝ} (h0 : -1 < x) (h1 : x < 1) :
    HasDerivAt lowGapThird (lowGapFourth x) x := by
  have hq : (1:ℝ) - x^2 ≠ 0 := by nlinarith
  have hq2 : ((1:ℝ) - x^2)^2 ≠ 0 := pow_ne_zero 2 hq
  have t1 := (hasDerivAt_const x (6*(49:ℝ)/64))
  have t2 := (artanh_hasDerivAt h0 h1).const_mul (6*β)
  have t3 := ((hasDerivAt_id' x).const_mul (6*β)).div ((hasDerivAt_pow 2 x).const_sub 1) hq
  have t4 := (((hasDerivAt_id' x).const_mul 2).mul
    (((hasDerivAt_pow 2 x).const_mul β).const_sub α)).div
    (((hasDerivAt_pow 2 x).const_sub 1).pow 2) hq2
  have hs := ((t1.sub t2).sub t3).add t4
  refine hs.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.pow_apply]; unfold lowGapFourth; field_simp; push_cast; ring

/-! ### Mean value theorem on subintervals of `(-1,1)` -/

theorem mvt {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b) (ha : -1 < a) (hb : b < 1)
    (hd : ∀ x, -1 < x → x < 1 → HasDerivAt f (f' x) x) :
    ∃ ξ ∈ Set.Ioo a b, f' ξ = (f b - f a) / (b - a) := by
  apply exists_hasDerivAt_eq_slope f f' hab
  · intro x hx
    exact (hd x (by linarith [hx.1]) (by linarith [hx.2])).continuousAt.continuousWithinAt
  · intro x hx
    exact hd x (by linarith [hx.1]) (by linarith [hx.2])

/-! ### Shape of `B0''` -/

/-- The fourth-derivative numerator increases with `r²` for `r² ≤ 1` (needs `α, β > 0`). -/
theorem numerator_mono (F : LowFixedFacts) {x y : ℝ} (hxy : x < y) (hy : y ≤ 1) :
    α * (1 + 3 * x) - β * (x^2 - 3 * x + 6) < α * (1 + 3 * y) - β * (y^2 - 3 * y + 6) := by
  have ha := F.alpha_lower
  have hb := F.beta_lower
  have e : (α * (1 + 3 * y) - β * (y^2 - 3 * y + 6)) - (α * (1 + 3 * x) - β * (x^2 - 3 * x + 6))
      = (y - x) * (3 * α + β + β * ((1 - x) + (1 - y))) := by ring
  have : 0 < (y - x) * (3 * α + β + β * ((1 - x) + (1 - y))) := by
    apply mul_pos (by linarith)
    have : 0 ≤ β * ((1 - x) + (1 - y)) := mul_nonneg hb.le (by linarith)
    linarith
  linarith

/-- No interior maximum: on `5/8 ≤ a ≤ r ≤ b < 1`, `B0'' r ≤ max (B0'' a) (B0'' b)`. -/
theorem second_le_max (F : LowFixedFacts) {a r b : ℝ} (ha : 5/8 ≤ a) (har : a ≤ r)
    (hrb : r ≤ b) (hb : b < 1) :
    lowGapSecond r ≤ max (lowGapSecond a) (lowGapSecond b) := by
  by_contra hc
  push Not at hc
  have hfa : lowGapSecond a < lowGapSecond r := lt_of_le_of_lt (le_max_left _ _) hc
  have hfb : lowGapSecond b < lowGapSecond r := lt_of_le_of_lt (le_max_right _ _) hc
  have har' : a < r := lt_of_le_of_ne har (by rintro rfl; exact lt_irrefl _ hfa)
  have hrb' : r < b := lt_of_le_of_ne hrb (by rintro rfl; exact lt_irrefl _ hfb)
  have dom2 := fun x (h0 : -1 < x) (h1 : x < 1) => lowGapSecond_hasDerivAt h0 h1
  have dom3 := fun x (h0 : -1 < x) (h1 : x < 1) => lowGapThird_hasDerivAt h0 h1
  obtain ⟨ξ₁, hξ₁, e₁⟩ := mvt har' (by linarith) (by linarith) dom2
  obtain ⟨ξ₂, hξ₂, e₂⟩ := mvt hrb' (by linarith) hb dom2
  have g1 : 0 < lowGapThird ξ₁ := by rw [e₁]; exact div_pos (by linarith) (by linarith)
  have g2 : lowGapThird ξ₂ < 0 := by
    rw [e₂]; exact div_neg_of_neg_of_pos (by linarith) (by linarith)
  have g0 := F.third_at_start
  have h58 : (5:ℝ)/8 < ξ₁ := by linarith [hξ₁.1]
  obtain ⟨η₁, hη₁, f₁⟩ := mvt h58 (by norm_num) (by linarith [hξ₁.2]) dom3
  have h12 : ξ₁ < ξ₂ := by linarith [hξ₁.2, hξ₂.1]
  obtain ⟨η₂, hη₂, f₂⟩ := mvt h12 (by linarith [hξ₁.1]) (by linarith [hξ₂.2]) dom3
  have p1 : 0 < lowGapFourth η₁ := by rw [f₁]; exact div_pos (by linarith) (by linarith)
  have p2 : lowGapFourth η₂ < 0 := by
    rw [f₂]; exact div_neg_of_neg_of_pos (by linarith) (by linarith)
  have hη₁0 : 0 < η₁ := by linarith [hη₁.1]
  have hη₂1 : η₂ < 1 := by linarith [hη₂.2, hξ₂.2]
  have hη12 : η₁ < η₂ := by linarith [hη₁.2, hη₂.1]
  have den₁ : 0 < (1 - η₁^2)^3 := pow_pos (by nlinarith) 3
  have den₂ : 0 < (1 - η₂^2)^3 := pow_pos (by nlinarith) 3
  have N₁ : 0 < α * (1 + 3 * η₁^2) - β * ((η₁^2)^2 - 3 * η₁^2 + 6) := by
    by_contra hn; push Not at hn
    have : lowGapFourth η₁ ≤ 0 := by
      unfold lowGapFourth
      apply div_nonpos_of_nonpos_of_nonneg _ den₁.le
      nlinarith
    linarith
  have mono := numerator_mono F (x := η₁^2) (y := η₂^2)
    (by nlinarith) (by nlinarith)
  have : 0 < lowGapFourth η₂ := by
    unfold lowGapFourth
    apply div_pos _ den₂
    nlinarith
  linarith

/-! ### Sign of `B0'` and positivity of `B0` -/

theorem cutoff_facts (F : LowFixedFacts) : (4:ℝ)/5 < lowCutoff ∧ lowCutoff < 1 :=
  ⟨F.cutoff_lower, F.cutoff_upper⟩

theorem lowGapFirst_neg_early (F : LowFixedFacts) {r : ℝ} (h1 : 5/8 ≤ r) (h2 : r ≤ 4/5) :
    lowGapFirst r < 0 := by
  have s0 := F.first_at_start
  rcases eq_or_lt_of_le h1 with e | hlt
  · rw [← e]; linarith
  obtain ⟨ξ, hξ, e⟩ := mvt hlt (by norm_num) (by linarith)
    (fun x h0 h1 => lowGapFirst_hasDerivAt h0 h1)
  have hmax := second_le_max F (a := 5/8) (r := ξ) (b := 4/5) le_rfl hξ.1.le
    (by linarith [hξ.2]) (by norm_num)
  have hs : lowGapSecond ξ < 7/30 := by
    have := F.second_at_start; have := F.second_at_join
    exact lt_of_le_of_lt hmax (max_lt (by linarith) (by linarith))
  have hpos : 0 < r - 5/8 := by linarith
  have eq : lowGapFirst r = lowGapFirst (5/8) + lowGapSecond ξ * (r - 5/8) := by
    rw [e, div_mul_cancel₀ _ hpos.ne']; ring
  rw [eq]
  nlinarith

theorem lowGapFirst_neg (F : LowFixedFacts) {r : ℝ} (h1 : 5/8 ≤ r) (h2 : r ≤ lowCutoff) :
    lowGapFirst r < 0 := by
  obtain ⟨c1, c2⟩ := cutoff_facts F
  rcases le_or_gt r (4/5) with hle | hgt
  · exact lowGapFirst_neg_early F h1 hle
  obtain ⟨ξ, hξ, e⟩ := mvt hgt (by norm_num) (by linarith)
    (fun x h0 h1 => lowGapFirst_hasDerivAt h0 h1)
  have hmax := second_le_max F (a := 4/5) (r := ξ) (b := lowCutoff) (by norm_num) hξ.1.le
    (by linarith [hξ.2]) c2
  have hs : lowGapSecond ξ < 0 := by
    have := F.second_at_join; have := F.second_at_end
    exact lt_of_le_of_lt hmax (max_lt (by linarith) (by linarith))
  have f45 := lowGapFirst_neg_early F (r := 4/5) (by norm_num) le_rfl
  have hpos : 0 < r - 4/5 := by linarith
  have eq : lowGapFirst r = lowGapFirst (4/5) + lowGapSecond ξ * (r - 4/5) := by
    rw [e, div_mul_cancel₀ _ hpos.ne']; ring
  rw [eq]
  nlinarith

/-- Reduction of low.tex `B0 ≥ B0(r₁) > 0` to `LowFixedFacts`. -/
theorem lowGap_pos (F : LowFixedFacts) {r : ℝ} (h1 : 5/8 ≤ r) (h2 : r ≤ lowCutoff) :
    0 < lowGap r := by
  obtain ⟨c1, c2⟩ := cutoff_facts F
  have hend := F.value_at_end
  rcases eq_or_lt_of_le h2 with e | hlt
  · rw [e]; linarith
  obtain ⟨ξ, hξ, e⟩ := mvt hlt (by linarith) c2 (fun x h0 h1 => lowGap_hasDerivAt h0 h1)
  have hneg := lowGapFirst_neg F (r := ξ) (by linarith [hξ.1]) hξ.2.le
  have hpos : 0 < lowCutoff - r := by linarith
  have eq : lowGap r = lowGap lowCutoff - lowGapFirst ξ * (lowCutoff - r) := by
    rw [e, div_mul_cancel₀ _ hpos.ne']; ring
  rw [eq]
  nlinarith

/-- Reduction of low.tex's nonnegative mean coefficient to `LowFixedFacts`
(only `α > 53/40`, `0 < β < 17/20` are used), on `[5/8, 1]`. -/
theorem mean_coefficient_nonneg (F : LowFixedFacts) {r : ℝ} (h1 : 5/8 ≤ r) (h2 : r ≤ 1) :
    0 ≤ 1/2 - lowCoefficient r * (1 - 2 * r^2 + r^3) := by
  have ha := F.alpha_lower
  have hb0 := F.beta_lower
  have hb1 := F.beta_upper
  have hr2 : r^2 ≤ 1 := by nlinarith
  have hbr : β * r^2 ≤ 17/20 * r^2 := by nlinarith
  have hden : 0 < α - β * r^2 := by nlinarith
  have key : 2 * (1 - 2 * r^2 + r^3) ≤ α - β * r^2 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ r - 5/8) (by linarith : (0:ℝ) ≤ 1 - r),
      mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ r - 5/8) (by linarith : (0:ℝ) ≤ 1 - r))
        (by linarith : (0:ℝ) ≤ r)]
  unfold lowCoefficient
  rw [sub_nonneg, one_div, inv_mul_eq_div, div_le_iff₀ hden]
  linarith

end MostInformativeBit.LowGapCalculus
