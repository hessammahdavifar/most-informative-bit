import MostInformativeBit.MeanCorrection
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Slope

/-! Tangent quadratic minorants of `source/low.tex` (Section "Tangent Quadratic Minorants").

For `0 < t < 1`:
`A t = log (2/(1+t)) / (1-t)^2`, `z t = 2t - artanh t / A t`, `Q t s = A t (1-s)(1+s-z t)`.
Main result `tangent_minorant`: `Q t s ≤ h s` for `0 ≤ s ≤ 1`.

Proof. `D = h - Q t` satisfies `D t = D' t = D 1 = 0` and `D'' = 2A - 1/(1-s^2)` is
antitone on `(0,1)`, so `D'` is concave there. If `D s₀ < 0`, the mean value theorem produces
three points of `(0,1)` at which the values of `D'` contradict concavity (slope comparison).

Second result `weighted_minorant`: the combination of two contacts `t₀, t₁` with
`z t₀ < z t₁` and `z t₀ ≤ w ≤ z t₁` gives `h s ≥ c (1-s)(1+s-w)` with
`c = 1/(α - β w)`, `β = (1/A₀ - 1/A₁)/(z₁ - z₀)`, `α = 1/A₀ + β z₀`.
-/

namespace MostInformativeBit.TangentMinorant

open MostInformativeBit MostInformativeBit.MeanCorrection

noncomputable def A (t : ℝ) : ℝ := Real.log (2 / (1 + t)) / (1 - t) ^ 2

noncomputable def z (t : ℝ) : ℝ := 2 * t - Real.artanh t / A t

noncomputable def Q (t s : ℝ) : ℝ := A t * (1 - s) * (1 + s - z t)

theorem A_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : 0 < A t := by
  unfold A
  apply div_pos _ (by nlinarith)
  apply Real.log_pos
  rw [lt_div_iff₀ (by linarith)]
  linarith

theorem artanh_eq_dv1 {x : ℝ} (h0 : -1 < x) (h1 : x < 1) : Real.artanh x = dv1 x := by
  rw [Real.artanh_eq_half_log ⟨h0.le, h1.le⟩, dv1,
    Real.log_div (by linarith : (1:ℝ) + x ≠ 0).symm.symm (by linarith : (1:ℝ) - x ≠ 0)]
  ring

/-- `h` near an interior point equals `log 2 - dv`. -/
theorem h_hasDerivAt {s : ℝ} (h0 : -1 < s) (h1 : s < 1) :
    HasDerivAt h (-dv1 s) s := by
  have hd : HasDerivAt (fun y => Real.log 2 - dv y) (-dv1 s) s := by
    simpa using (dv_hasDerivAt h0 h1).const_sub (Real.log 2)
  apply hd.congr_of_eventuallyEq
  have hU : Set.Ioo (-1:ℝ) 1 ∈ nhds s := Ioo_mem_nhds h0 h1
  filter_upwards [hU] with y hy
  rw [h_eq, phi_eq_dv hy.1 hy.2]

theorem h_one : h 1 = 0 := by simp [h]

theorem h_continuous : Continuous h := by
  unfold h; fun_prop

/-- Contact value `Q t t = h t`. -/
theorem Q_contact {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : Q t t = h t := by
  have hA := A_pos ht0 ht1
  have hp : (1:ℝ) + t ≠ 0 := by linarith
  have hm : (1:ℝ) - t ≠ 0 := by linarith
  have hm2 : (1 - t) ^ 2 ≠ 0 := pow_ne_zero 2 hm
  rw [h_eq, phi_eq_dv (by linarith) ht1]
  unfold Q z
  rw [artanh_eq_dv1 (by linarith) ht1]
  have hAe : A t * (1 - t) ^ 2 = Real.log 2 - Real.log (1 + t) := by
    unfold A
    rw [div_mul_cancel₀ _ hm2, Real.log_div two_ne_zero hp]
  have expand : A t * (1 - t) * (1 + t - (2 * t - dv1 t / A t)) =
      A t * (1 - t) ^ 2 + (1 - t) * dv1 t := by
    field_simp
    ring
  rw [expand, hAe]
  unfold dv1 dv
  ring

/-- `D = h - Q t`, its derivative `D1` and second derivative `D2`. -/
noncomputable def D (t s : ℝ) : ℝ := h s - Q t s
noncomputable def D1 (t s : ℝ) : ℝ := -dv1 s - A t * (z t - 2 * s)
noncomputable def D2 (t s : ℝ) : ℝ := 2 * A t - dv2 s

theorem D_hasDerivAt (t : ℝ) {s : ℝ} (h0 : -1 < s) (h1 : s < 1) :
    HasDerivAt (D t) (D1 t s) s := by
  have hq : HasDerivAt (fun y => Q t y) (A t * (z t - 2 * s)) s := by
    have := (((hasDerivAt_id' s).const_sub 1).const_mul (A t)).mul
      (((hasDerivAt_id' s).const_add 1).sub_const (z t))
    refine this.congr_deriv ?_
    ring
  exact ((h_hasDerivAt h0 h1).sub hq).congr_deriv (by unfold D1; ring)

theorem D1_hasDerivAt (t : ℝ) {s : ℝ} (h0 : -1 < s) (h1 : s < 1) :
    HasDerivAt (D1 t) (D2 t s) s := by
  have hl : HasDerivAt (fun y => A t * (z t - 2 * y)) (A t * -(2 * 1)) s :=
    (((hasDerivAt_id' s).const_mul 2).const_sub (z t)).const_mul (A t)
  exact ((dv1_hasDerivAt h0 h1).neg.sub hl).congr_deriv (by unfold D2; ring)

theorem D1_contact {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : D1 t t = 0 := by
  have hA := A_pos ht0 ht1
  unfold D1 z
  rw [artanh_eq_dv1 (by linarith) ht1]
  field_simp
  ring

theorem D_contact {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : D t t = 0 := by
  unfold D; rw [Q_contact ht0 ht1]; ring

theorem D_one (t : ℝ) : D t 1 = 0 := by
  unfold D Q; rw [h_one]; ring

theorem D_continuous (t : ℝ) : Continuous (D t) := by
  unfold D Q
  exact h_continuous.sub (by fun_prop)

/-- `dv2` is monotone on `[0,1)`, hence `D2` is antitone there. -/
theorem dv2_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y < 1) : dv2 x ≤ dv2 y := by
  have e : ∀ u : ℝ, -1 < u → u < 1 → dv2 u = 1 / (1 - u ^ 2) := by
    intro u h0 h1
    have hp : (1:ℝ) + u ≠ 0 := by linarith
    have hm : (1:ℝ) - u ≠ 0 := by linarith
    have hq : (1:ℝ) - u ^ 2 ≠ 0 := by nlinarith
    unfold dv2
    field_simp
    ring
  rw [e x (by linarith) (by linarith), e y (by linarith) hy]
  apply one_div_le_one_div_of_le (by nlinarith)
  nlinarith

theorem D1_concave (t : ℝ) : ConcaveOn ℝ (Set.Ioo (0:ℝ) 1) (D1 t) := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ioo 0 1)
  · intro s hs
    exact (D1_hasDerivAt t (by linarith [hs.1]) hs.2).continuousAt.continuousWithinAt
  · rw [isOpen_Ioo.interior_eq]
    intro s hs
    exact (D1_hasDerivAt t (by linarith [hs.1]) hs.2).differentiableAt.differentiableWithinAt
  · rw [isOpen_Ioo.interior_eq]
    intro x hx y hy hxy
    rw [(D1_hasDerivAt t (by linarith [hx.1]) hx.2).deriv,
      (D1_hasDerivAt t (by linarith [hy.1]) hy.2).deriv]
    unfold D2
    linarith [dv2_mono hx.1.le hxy hy.2]

/-- Mean value theorem for `D t` on `[a,b] ⊆ [0,1]`. -/
theorem D_mvt (t : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ c ∈ Set.Ioo a b, D1 t c = (D t b - D t a) / (b - a) :=
  exists_hasDerivAt_eq_slope (D t) (D1 t) hab (D_continuous t).continuousOn
    (fun x hx => D_hasDerivAt t (by linarith [hx.1]) (by linarith [hx.2]))

/-- The tangent entropy minorant (low.tex, (entropy-tangent-family)). -/
theorem tangent_minorant {t s : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Q t s ≤ h s := by
  have key : 0 ≤ D t s := by
    by_contra hneg
    push Not at hneg
    have hcc := D1_concave t
    have hst : s ≠ t := by intro e; rw [e, D_contact ht0 ht1] at hneg; exact lt_irrefl _ hneg
    have hs1' : s ≠ 1 := by intro e; rw [e, D_one] at hneg; exact lt_irrefl _ hneg
    have hslt : s < 1 := lt_of_le_of_ne hs1 hs1'
    rcases lt_or_gt_of_ne hst with hlt | hgt
    · -- s < t: slope of D1 on [ξ, t] is negative, on [t, ξ₂] is zero
      obtain ⟨ξ, hξ, hξv⟩ := D_mvt t hs0 hlt ht1.le
      obtain ⟨ξ₂, hξ₂, hξ₂v⟩ := D_mvt t ht0.le ht1 le_rfl
      rw [D_contact ht0 ht1] at hξv
      rw [D_one, D_contact ht0 ht1] at hξ₂v
      have hpos : 0 < D1 t ξ := by
        rw [hξv]; apply div_pos (by linarith) (by linarith [hξ.2])
      have hzero : D1 t ξ₂ = 0 := by rw [hξ₂v]; simp
      have hsl := hcc.slope_anti_adjacent (x := ξ) (y := t) (z := ξ₂)
        ⟨by linarith [hξ.1], by linarith [hξ.2]⟩ ⟨by linarith [hξ₂.1], hξ₂.2⟩ hξ.2 hξ₂.1
      rw [hzero, D1_contact ht0 ht1, sub_self, zero_div] at hsl
      have : (0 - D1 t ξ) / (t - ξ) < 0 :=
        div_neg_of_neg_of_pos (by linarith) (by linarith [hξ.2])
      linarith
    · -- t < s < 1: D1 negative on (t, s), positive on (s, 1): contradicts concavity
      obtain ⟨ξ₁, hξ₁, hξ₁v⟩ := D_mvt t ht0.le hgt hs1
      obtain ⟨ξ₂, hξ₂, hξ₂v⟩ := D_mvt t hs0 hslt le_rfl
      rw [D_contact ht0 ht1] at hξ₁v
      rw [D_one] at hξ₂v
      have hneg1 : D1 t ξ₁ < 0 := by
        rw [hξ₁v]; exact div_neg_of_neg_of_pos (by linarith) (by linarith)
      have hpos2 : 0 < D1 t ξ₂ := by
        rw [hξ₂v]; exact div_pos (by linarith) (by linarith)
      have hsl := hcc.slope_anti_adjacent (x := t) (y := ξ₁) (z := ξ₂)
        ⟨ht0, ht1⟩ ⟨by linarith [hξ₂.1, hξ₁.1], hξ₂.2⟩ hξ₁.1 (by linarith [hξ₁.2, hξ₂.1])
      rw [D1_contact ht0 ht1, sub_zero] at hsl
      have l : 0 < (D1 t ξ₂ - D1 t ξ₁) / (ξ₂ - ξ₁) :=
        div_pos (by linarith) (by linarith [hξ₁.2, hξ₂.1])
      have r : D1 t ξ₁ / (ξ₁ - t) < 0 := div_neg_of_neg_of_pos hneg1 (by linarith [hξ₁.1])
      linarith
  unfold D at key
  linarith

/-- Weighted two-contact minorant (low.tex, (minorant)), for general admissible contacts. -/
theorem weighted_minorant {t₀ t₁ w s : ℝ} (h00 : 0 < t₀) (h01 : t₀ < 1)
    (h10 : 0 < t₁) (h11 : t₁ < 1) (hz : z t₀ < z t₁)
    (hw0 : z t₀ ≤ w) (hw1 : w ≤ z t₁) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    let β := (1 / A t₀ - 1 / A t₁) / (z t₁ - z t₀)
    let α := 1 / A t₀ + β * z t₀
    0 < α - β * w ∧ 1 / (α - β * w) * (1 - s) * (1 + s - w) ≤ h s := by
  intro β α
  have hA0 := A_pos h00 h01
  have hA1 := A_pos h10 h11
  have hd : 0 < z t₁ - z t₀ := by linarith
  set μ := (z t₁ - w) / (z t₁ - z t₀) with hμ
  have hμ0 : 0 ≤ μ := div_nonneg (by linarith) hd.le
  have hμ1 : μ ≤ 1 := by rw [hμ, div_le_one hd]; linarith
  have hwμ : w = μ * z t₀ + (1 - μ) * z t₁ := by
    rw [hμ]; field_simp; ring
  -- α - β w is the convex combination of 1/A₀ and 1/A₁
  have hden : α - β * w = μ / A t₀ + (1 - μ) / A t₁ := by
    simp only [α, β]; rw [hwμ, hμ]; field_simp; ring
  have hpos : 0 < α - β * w := by
    rw [hden]
    rcases eq_or_lt_of_le hμ1 with e | lt
    · rw [e]; simp; positivity
    · have : 0 < 1 - μ := by linarith
      have := div_pos this hA1
      have := div_nonneg hμ0 hA0.le
      linarith
  refine ⟨hpos, ?_⟩
  set c := 1 / (α - β * w) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hQ0 := tangent_minorant h00 h01 hs0 hs1
  have hQ1 := tangent_minorant h10 h11 hs0 hs1
  have l0 : 0 ≤ μ * c / A t₀ := by positivity
  have l1 : 0 ≤ (1 - μ) * c / A t₁ := div_nonneg (mul_nonneg (by linarith) hcpos.le) hA1.le
  have hsum : μ * c / A t₀ + (1 - μ) * c / A t₁ = 1 := by
    have : μ * c / A t₀ + (1 - μ) * c / A t₁ = c * (α - β * w) := by rw [hden]; ring
    rw [this, hc, one_div, inv_mul_cancel₀ hpos.ne']
  have hcomb : μ * c / A t₀ * Q t₀ s + (1 - μ) * c / A t₁ * Q t₁ s =
      c * (1 - s) * (1 + s - w) := by
    unfold Q; rw [hwμ]; field_simp; ring
  have := add_le_add (mul_le_mul_of_nonneg_left hQ0 l0) (mul_le_mul_of_nonneg_left hQ1 l1)
  rw [hcomb, ← add_mul, hsum, one_mul] at this
  exact this

/-- The manuscript's instance `w = r^2`. -/
theorem weighted_minorant_sq {t₀ t₁ r s : ℝ} (h00 : 0 < t₀) (h01 : t₀ < 1)
    (h10 : 0 < t₁) (h11 : t₁ < 1) (hz : z t₀ < z t₁)
    (hr0 : z t₀ ≤ r ^ 2) (hr1 : r ^ 2 ≤ z t₁) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    let β := (1 / A t₀ - 1 / A t₁) / (z t₁ - z t₀)
    let α := 1 / A t₀ + β * z t₀
    1 / (α - β * r ^ 2) * (1 - s) * (1 + s - r ^ 2) ≤ h s :=
  (weighted_minorant h00 h01 h10 h11 hz hr0 hr1 hs0 hs1).2

end MostInformativeBit.TangentMinorant
