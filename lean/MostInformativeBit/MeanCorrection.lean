import MostInformativeBit.Definitions
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Mean correction (S7) of `source/scalar.tex`:
for `0 ≤ r ≤ 1`, `0 ≤ a`, `|m| + a ≤ 1`,
`phi m + (1-r^2)/2 * (h (m+r*a) + h (m-r*a)) ≥ (1-r^2) * h (r*a)`.

Route (the paper's convexity argument). Writing `h = log 2 - phi`, the claim is
`G m ≥ 0` for `G m = phi m - δ/2 (phi (m+b) + phi (m-b)) + δ phi b`, `δ = 1-r^2`, `b = r a`.
`G` is even with `G 0 = G' 0 = 0`, and on `0 ≤ m ≤ 1-a` its second derivative is
`r^2 E / (positive)`, where `E` is the manuscript's sign expression
`[1-(m+a)^2][1-(m-a)^2] + (1-r^2) a^2 (1-m^2-a^2) ≥ 0`.
-/

namespace MostInformativeBit.MeanCorrection

open MostInformativeBit

/-- Natural divergence from uniform, sign-mean form. Equals `phi` on `(-1,1)`. -/
noncomputable def dv (x : ℝ) : ℝ :=
  ((1+x) * Real.log (1+x) + (1-x) * Real.log (1-x)) / 2

noncomputable def dv1 (x : ℝ) : ℝ := (Real.log (1+x) - Real.log (1-x)) / 2

noncomputable def dv2 (x : ℝ) : ℝ := (1/(1+x) + 1/(1-x)) / 2

theorem phi_eq_dv {x : ℝ} (h0 : -1 < x) (h1 : x < 1) : phi x = dv x := by
  have hp : (1 - x) ≠ 0 := (by linarith : (0:ℝ) < 1 - x).ne'
  have hq : (1 + x) ≠ 0 := (by linarith : (0:ℝ) < 1 + x).ne'
  unfold phi h dv
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    show 1 - (1 - x) / 2 = (1 + x) / 2 by ring]
  simp only [Real.negMulLog]
  rw [Real.log_div hp two_ne_zero, Real.log_div hq two_ne_zero]
  ring

theorem h_eq (x : ℝ) : h x = Real.log 2 - phi x := by
  unfold phi; ring

theorem dv_neg (x : ℝ) : dv (-x) = dv x := by
  unfold dv
  rw [show (1:ℝ) + -x = 1 - x by ring, show (1:ℝ) - -x = 1 + x by ring]
  ring

theorem dv_zero : dv 0 = 0 := by simp [dv]

theorem dv1_neg (x : ℝ) : dv1 (-x) = -dv1 x := by
  unfold dv1
  rw [show (1:ℝ) + -x = 1 - x by ring, show (1:ℝ) - -x = 1 + x by ring]
  ring

theorem dv1_zero : dv1 0 = 0 := by simp [dv1]

theorem dv_hasDerivAt {x : ℝ} (h0 : -1 < x) (h1 : x < 1) :
    HasDerivAt dv (dv1 x) x := by
  have hp : 1 + x ≠ 0 := (by linarith : (0:ℝ) < 1 + x).ne'
  have hm : 1 - x ≠ 0 := (by linarith : (0:ℝ) < 1 - x).ne'
  have lp : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id' x).const_add 1
  have lm : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := (hasDerivAt_id' x).const_sub 1
  have hA := lp.mul (lp.log hp)
  have hB := lm.mul (lm.log hm)
  have hs := (hA.add hB).div_const 2
  refine hs.congr_deriv ?_
  unfold dv1
  field_simp
  ring

theorem dv1_hasDerivAt {x : ℝ} (h0 : -1 < x) (h1 : x < 1) :
    HasDerivAt dv1 (dv2 x) x := by
  have hp : 1 + x ≠ 0 := (by linarith : (0:ℝ) < 1 + x).ne'
  have hm : 1 - x ≠ 0 := (by linarith : (0:ℝ) < 1 - x).ne'
  have lp : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id' x).const_add 1
  have lm : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := (hasDerivAt_id' x).const_sub 1
  have hs := ((lp.log hp).sub (lm.log hm)).div_const 2
  refine hs.congr_deriv ?_
  unfold dv2
  field_simp
  ring

/-- Second-derivative sign: `dv2 m - δ/2 (dv2 (m+b) + dv2 (m-b)) ≥ 0`
with `δ = 1-r^2`, `b = r a`, on `0 ≤ m ≤ 1-a`. -/
theorem second_nonneg {r a m : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (ha0 : 0 < a)
    (hm0 : 0 ≤ m) (hma : m + a ≤ 1) :
    0 ≤ dv2 m - (1 - r^2)/2 * (dv2 (m + r*a) + dv2 (m - r*a)) := by
  have hb0 : 0 ≤ r * a := mul_nonneg hr0 ha0.le
  have hba : r * a < a := by nlinarith
  have h1 : 0 < 1 - m := by linarith
  have h2 : 0 < 1 + m := by linarith
  have h3 : 0 < 1 - (m + r*a) := by linarith
  have h4 : 0 < 1 + (m + r*a) := by linarith
  have h5 : 0 < 1 - (m - r*a) := by linarith
  have h6 : 0 < 1 + (m - r*a) := by linarith
  have key : dv2 m - (1 - r^2)/2 * (dv2 (m + r*a) + dv2 (m - r*a)) =
      r^2 * ((1-(m+a))*(1+(m+a))*(1-(m-a))*(1+(m-a)) + (1-r^2)*a^2*(1-m^2-a^2)) /
        ((1-m)*(1+m)*((1-(m+r*a))*(1+(m+r*a)))*((1-(m-r*a))*(1+(m-r*a)))) := by
    unfold dv2
    field_simp
    ring
  rw [key]
  apply div_nonneg _ (by positivity)
  apply mul_nonneg (sq_nonneg r)
  have e1 : 0 ≤ 1 - (m + a) := by linarith
  have e2 : 0 ≤ 1 + (m + a) := by linarith
  have e3 : 0 ≤ 1 - (m - a) := by linarith
  have e4 : 0 ≤ 1 + (m - a) := by linarith
  have e5 : 0 ≤ 1 - r^2 := by nlinarith
  have e6 : 0 ≤ 1 - m^2 - a^2 := by nlinarith
  have p1 : 0 ≤ (1-(m+a))*(1+(m+a))*(1-(m-a))*(1+(m-a)) := by positivity
  have p2 : 0 ≤ (1-r^2)*a^2*(1-m^2-a^2) := by positivity
  linarith

/-- Core: `G y ≥ 0` on `0 ≤ y ≤ 1-a`, in the interior parameter range. -/
theorem core_nonneg {r a : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (ha0 : 0 < a) (ha1 : a ≤ 1)
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 - a) :
    0 ≤ dv y - (1 - r^2)/2 * (dv (y + r*a) + dv (y - r*a)) + (1 - r^2) * dv (r*a) := by
  set δ := 1 - r^2 with hδ
  set b := r * a with hb
  have hb0 : 0 ≤ b := mul_nonneg hr0 ha0.le
  have hba : b < a := by rw [hb]; nlinarith
  -- all arguments stay in (-1,1) on the interval
  have dom : ∀ z ∈ Set.Icc (0:ℝ) (1 - a),
      (-1 < z ∧ z < 1) ∧ (-1 < z + b ∧ z + b < 1) ∧ (-1 < z - b ∧ z - b < 1) := by
    intro z hz
    obtain ⟨hz0, hz1⟩ := hz
    refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  let G1 : ℝ → ℝ := fun z => dv1 z - δ/2 * (dv1 (z + b) + dv1 (z - b))
  let G : ℝ → ℝ := fun z => dv z - δ/2 * (dv (z + b) + dv (z - b)) + δ * dv b
  have hG1 : ∀ z ∈ Set.Icc (0:ℝ) (1 - a),
      HasDerivAt G1 (dv2 z - δ/2 * (dv2 (z + b) + dv2 (z - b))) z := by
    intro z hz
    obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := dom z hz
    have hp : HasDerivAt (fun w => dv1 (w + b)) (dv2 (z + b)) z :=
      (dv1_hasDerivAt b1 b2).comp_add_const z b
    have hm : HasDerivAt (fun w => dv1 (w - b)) (dv2 (z - b)) z :=
      (dv1_hasDerivAt c1 c2).comp_sub_const z b
    exact (dv1_hasDerivAt a1 a2).sub ((hp.add hm).const_mul (δ/2))
  have hG : ∀ z ∈ Set.Icc (0:ℝ) (1 - a), HasDerivAt G (G1 z) z := by
    intro z hz
    obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := dom z hz
    have hp : HasDerivAt (fun w => dv (w + b)) (dv1 (z + b)) z :=
      (dv_hasDerivAt b1 b2).comp_add_const z b
    have hm : HasDerivAt (fun w => dv (w - b)) (dv1 (z - b)) z :=
      (dv_hasDerivAt c1 c2).comp_sub_const z b
    exact ((dv_hasDerivAt a1 a2).sub ((hp.add hm).const_mul (δ/2))).add_const (δ * dv b)
  have hy : y ∈ Set.Icc (0:ℝ) (1 - a) := ⟨hy0, hy1⟩
  have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) (1 - a) := ⟨le_rfl, by linarith⟩
  -- Step 1: G1 is monotone, so G1 ≥ G1 0 = 0
  have mono1 : MonotoneOn G1 (Set.Icc (0:ℝ) (1 - a)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 - a))
    · intro z hz; exact (hG1 z hz).continuousAt.continuousWithinAt
    · intro z hz
      exact (hG1 z (interior_subset hz)).differentiableAt.differentiableWithinAt
    · intro z hz
      have hz' : z ∈ Set.Icc (0:ℝ) (1 - a) := interior_subset hz
      rw [(hG1 z hz').deriv]
      exact second_nonneg hr0 hr1 ha0 hz'.1 (by linarith [hz'.2])
  have G1_zero : G1 0 = 0 := by
    simp only [G1, zero_add, zero_sub, dv1_neg, dv1_zero]; ring
  have G1_nonneg : ∀ z ∈ Set.Icc (0:ℝ) (1 - a), 0 ≤ G1 z := by
    intro z hz
    have := mono1 h0 hz hz.1
    rwa [G1_zero] at this
  -- Step 2: G is monotone, so G ≥ G 0 = 0
  have mono : MonotoneOn G (Set.Icc (0:ℝ) (1 - a)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 - a))
    · intro z hz; exact (hG z hz).continuousAt.continuousWithinAt
    · intro z hz
      exact (hG z (interior_subset hz)).differentiableAt.differentiableWithinAt
    · intro z hz
      have hz' : z ∈ Set.Icc (0:ℝ) (1 - a) := interior_subset hz
      rw [(hG z hz').deriv]
      exact G1_nonneg z hz'
  have G_zero : G 0 = 0 := by
    simp only [G, zero_add, zero_sub, dv_neg, dv_zero]; ring
  have := mono h0 hy hy0
  rw [G_zero] at this
  exact this

/-- The manuscript's (S7), on its full closed domain. -/
theorem mean_correction {r a m : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a)
    (hma : |m| + a ≤ 1) :
    phi m + (1 - r^2)/2 * (h (m + r*a) + h (m - r*a)) ≥ (1 - r^2) * h (r*a) := by
  simp only [h_eq]
  rw [ge_iff_le, ← sub_nonneg]
  have hphi := phi_nonneg m
  rcases eq_or_lt_of_le hr1 with hr | hr
  · -- r = 1: δ = 0
    subst hr; norm_num; exact hphi
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · -- a = 0
    subst ha0
    simp only [mul_zero, add_zero, sub_zero, phi_zero]
    nlinarith [sq_nonneg r]
  -- interior parameters: 0 ≤ r < 1, 0 < a
  have habs := abs_nonneg m
  have ha1 : a ≤ 1 := by linarith
  have hm1 : |m| ≤ 1 - a := by linarith
  have hmlt : |m| < 1 := by linarith
  have hb0 : 0 ≤ r * a := mul_nonneg hr0 ha0.le
  have hba : r * a < a := by nlinarith
  obtain ⟨hml, hmu⟩ := abs_le.mp hm1
  rw [phi_eq_dv (x := m) (by linarith) (by linarith),
    phi_eq_dv (x := m + r*a) (by linarith) (by linarith),
    phi_eq_dv (x := m - r*a) (by linarith) (by linarith),
    phi_eq_dv (x := r*a) (by linarith) (by linarith)]
  rcases le_total 0 m with hm0 | hm0
  · have := core_nonneg hr0 hr ha0 ha1 hm0 hmu
    linarith
  · have := core_nonneg hr0 hr ha0 ha1 (y := -m) (by linarith) (by linarith)
    rw [dv_neg, show -m + r*a = -(m - r*a) by ring, show -m - r*a = -(m + r*a) by ring,
      dv_neg, dv_neg] at this
    linarith

end MostInformativeBit.MeanCorrection
