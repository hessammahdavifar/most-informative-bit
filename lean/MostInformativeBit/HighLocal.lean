import MostInformativeBit.LocalPropagation
import MostInformativeBit.ChannelBounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-! manual-local.tex: the local cutoff for `ell ≥ 7/2`,
`a_cut = 1/(1 + (8/3) e^{-ell})`, on the whole unbounded half-line. -/
namespace MostInformativeBit.HighLocal
open Set

/-- The rational local cutoff (eq. `rational-local-cutoff`). -/
noncomputable def aCut (ell : ℝ) : ℝ := 1/(1+(8/3)*Real.exp (-ell))

lemma exp_seven_halves_gt : (32:ℝ) < Real.exp (7/2) := by
  have he := Real.exp_one_gt_d9
  have hq := Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 1/2 by norm_num)
  have hsplit : Real.exp (7/2) = Real.exp 1*Real.exp 1*Real.exp 1*Real.exp (1/2) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; norm_num
  rw [hsplit]
  have h1 : (2.7182818283:ℝ)^3 < Real.exp 1*Real.exp 1*Real.exp 1 := by
    have := Real.exp_pos 1
    nlinarith [mul_lt_mul'' he he (by norm_num) (by norm_num)]
  nlinarith [Real.exp_pos (1/2)]

lemma log_four_thirds_lt : Real.log (4/3) < 7/24 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have hq := Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 7/24 by norm_num)
  linarith

/-- `ell e^{-ell} ≤ (7/2) e^{-7/2} < 7/64` for `ell ≥ 7/2`. -/
lemma ell_mul_exp_le {ell : ℝ} (hell : 7/2 ≤ ell) : ell*Real.exp (-ell) ≤ 7/64 := by
  have hd : ∀ y, HasDerivAt (fun y => y*Real.exp (-y)) ((1-y)*Real.exp (-y)) y := by
    intro y
    have hh := (hasDerivAt_id' y).mul ((Real.hasDerivAt_exp (-y)).comp y (hasDerivAt_neg y))
    refine hh.congr_deriv ?_
    simp only [Function.comp_apply]
    ring
  have ha : AntitoneOn (fun y => y*Real.exp (-y)) (Ici (7/2)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici _)
    · intro y _
      exact (hd y).continuousAt.continuousWithinAt
    · intro y _
      exact (hd y).hasDerivWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have := Real.exp_pos (-y)
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [show (7/2:ℝ) < y from hy]) this.le
  have hh := ha self_mem_Ici (show ell ∈ Ici (7/2) from hell) hell
  simp only at hh
  have h32 := exp_seven_halves_gt
  have hinv : Real.exp (-(7/2)) < 1/32 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) h32
  linarith

set_option maxHeartbeats 1000000 in
/-- **manual-local.tex, local cutoff.** For `ell ≥ 7/2`, `r = tanh ell`:
`(1-r^2) h(r a_cut) - (1 - a_cut r^2) h(r) > 0`. -/
theorem local_cutoff {ell : ℝ} (hell : 7/2 ≤ ell) :
    0 < localMargin (Real.tanh ell) (aCut ell) := by
  set x := Real.exp (-ell) with hxdef
  have hx0 : 0 < x := Real.exp_pos _
  have h32 := exp_seven_halves_gt
  have hx1 : x ≤ 1/32 := by
    have : x ≤ Real.exp (-(7/2)) := Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_neg, inv_eq_one_div] at this
    exact this.trans (one_div_le_one_div_of_le (by norm_num) h32.le)
  have hlx : ell*x ≤ 7/64 := ell_mul_exp_le hell
  have hell0 : 0 ≤ ell := by linarith
  have hlogx : Real.log x = -ell := Real.log_exp _
  -- tanh in terms of x
  have hr : Real.tanh ell = (1-x^2)/(1+x^2) := by
    rw [ChannelBounds.tanh_eq_q]
    unfold ChannelBounds.q
    rw [show -2*ell = -ell + -ell by ring, Real.exp_add, ← hxdef]
    ring
  set S := 1+x^2 with hS
  set K := 3+8*x with hK
  set N := 4+3*x+4*x^2 with hN
  set W := 2+3*x+4*x^2+2*x^4 with hW
  have hS0 : 0 < S := by positivity
  have hK0 : 0 < K := by positivity
  have hN0 : 0 < N := by positivity
  set q := x*N/(K*S) with hq
  set t := x^2/S with ht
  unfold localMargin h aCut
  rw [hr, ← hxdef]
  have hqe : (1-(1-x^2)/(1+x^2)*(1/(1+8/3*x)))/2 = q := by
    rw [hq, hN, hK, hS]; field_simp; ring
  have hte : (1-(1-x^2)/(1+x^2))/2 = t := by
    rw [ht, hS]; field_simp; ring
  have h1r : 1-((1-x^2)/(1+x^2))^2 = 4*x^2/S^2 := by
    rw [hS]; field_simp; ring
  have h1ar : 1-1/(1+8/3*x)*((1-x^2)/(1+x^2))^2 = 4*x*W/(K*S^2) := by
    rw [hS, hK, hW]; field_simp; ring
  rw [hqe, hte, h1r, h1ar]
  -- ranges of q and t
  have hq0 : 0 < q := by positivity
  have hqs : q ≤ 1/25 := by
    rw [hq, div_le_iff₀ (by positivity)]
    nlinarith
  have ht0 : 0 < t := by positivity
  have ht1 : t < 1 := by rw [ht, div_lt_one hS0]; linarith
  -- lower bound for binEntropy q
  have hlogq : ell - 7/24 ≤ Real.log q⁻¹ := by
    have he : q⁻¹ = x⁻¹*(3/4*(4*K*S/(3*N))) := by
      rw [hq]; field_simp
    have hge : 1 ≤ 4*K*S/(3*N) := by
      rw [le_div_iff₀ (by positivity), hK, hS, hN]
      nlinarith
    rw [he, Real.log_mul (by positivity) (by positivity), Real.log_inv, hlogx,
      Real.log_mul (by norm_num) (by positivity)]
    have h34 : Real.log (3/4) = -Real.log (4/3) := by
      rw [← Real.log_inv]; norm_num
    have := Real.log_nonneg hge
    linarith [log_four_thirds_lt]
  have hlog1q : q ≤ Real.log (1-q)⁻¹ := by
    rw [Real.log_inv]
    linarith [Real.log_le_sub_one_of_pos (show 0 < 1-q by linarith)]
  have hbq : q*(ell - 7/24) + (1-q)*q ≤ Real.binEntropy q := by
    unfold Real.binEntropy
    nlinarith [mul_le_mul_of_nonneg_left hlogq hq0.le,
      mul_le_mul_of_nonneg_left hlog1q (show 0 ≤ 1-q by linarith)]
  -- upper bound for binEntropy t
  have hbt : Real.binEntropy t ≤ x^2 + 2*ell*t := by
    have hlt : Real.log t⁻¹ = Real.log S + 2*ell := by
      rw [ht, inv_div, Real.log_div hS0.ne' (by positivity), Real.log_pow, hlogx]
      push_cast; ring
    have hl1t : Real.log (1-t)⁻¹ = Real.log S := by
      congr 1; rw [ht]; field_simp; ring
    have hlS : Real.log S ≤ x^2 := by
      linarith [Real.log_le_sub_one_of_pos hS0]
    unfold Real.binEntropy
    rw [hlt, hl1t]
    nlinarith
  -- the bracket
  have hkey : 0 < N*(17/24 - q) - W*S - ell*x*(3+4*x+4*x^3) := by
    have hx2 : x^2 ≤ 1/1024 := by nlinarith
    have hx3 : x^3 ≤ 1/32768 := by nlinarith
    have hx4 : x^4 ≤ 1/1048576 := by nlinarith
    have hNl : 4 ≤ N := by
      have : 0 ≤ 3*x+4*x^2 := by positivity
      rw [hN]; linarith
    have hW1 : W ≤ 21/10 := by rw [hW]; linarith
    have hS1 : S ≤ 21/20 := by rw [hS]; linarith
    have hWS : W*S ≤ 21/10*(21/20) :=
      mul_le_mul hW1 hS1 hS0.le (by norm_num)
    have hP : 3+4*x+4*x^3 ≤ 16/5 := by linarith
    have hlx' : ell*x*(3+4*x+4*x^3) ≤ 7/64*(16/5) :=
      mul_le_mul hlx hP (by positivity) (by norm_num)
    have hNq : 4*(17/24 - 1/25) ≤ N*(17/24 - q) :=
      mul_le_mul hNl (by linarith) (by norm_num) hN0.le
    linarith
  have hA : 0 ≤ 4*x^2/S^2 := by positivity
  have hB : 0 ≤ 4*x*W/(K*S^2) := by positivity
  have hlow : 4*x^2/S^2*(q*(ell - 7/24) + (1-q)*q) - 4*x*W/(K*S^2)*(x^2 + 2*ell*t) ≤
      4*x^2/S^2*Real.binEntropy q - 4*x*W/(K*S^2)*Real.binEntropy t := by
    nlinarith [mul_le_mul_of_nonneg_left hbq hA, mul_le_mul_of_nonneg_left hbt hB]
  have hid : 4*x^2/S^2*(q*(ell - 7/24) + (1-q)*q) - 4*x*W/(K*S^2)*(x^2 + 2*ell*t) =
      4*x^3/(K*S^3)*(N*(17/24 - q) - W*S - ell*x*(3+4*x+4*x^3)) := by
    rw [hq, ht, hN, hW]
    field_simp
    ring
  have hfac : 0 < 4*x^3/(K*S^3) := by positivity
  linarith [mul_pos hfac hkey]

lemma aCut_mem {ell : ℝ} : 0 ≤ aCut ell ∧ aCut ell ≤ 1 := by
  unfold aCut
  have := Real.exp_pos (-ell)
  constructor
  · positivity
  · rw [div_le_one (by positivity)]; linarith

/-- The local condition (eq. `local`) throughout `[a_cut, 1]` (equality at `a = 1`). -/
theorem local_margin_nonneg {ell a : ℝ} (hell : 7/2 ≤ ell) (ha : aCut ell ≤ a) (ha1 : a ≤ 1) :
    0 ≤ localMargin (Real.tanh ell) a :=
  localMargin_nonneg_above (CenteredSupport.tanh_pos (by linarith)).le (Real.tanh_lt_one ell).le
    aCut_mem.1 ha ha1 (local_cutoff hell).le

/-- The source's condition in its displayed form:
`(1-ρ^2) h(ρ a) ≥ (1-ρ^2 a) h(ρ)` for `ρ = tanh ell`, `ell ≥ 7/2`, `a ∈ [a_cut, 1]`. -/
theorem local_condition {ell a : ℝ} (hell : 7/2 ≤ ell) (ha : aCut ell ≤ a) (ha1 : a ≤ 1) :
    (1-Real.tanh ell^2)*h (Real.tanh ell*a) ≥ (1-Real.tanh ell^2*a)*h (Real.tanh ell) := by
  have hh := local_margin_nonneg hell ha ha1
  unfold localMargin at hh
  rw [mul_comm (Real.tanh ell^2) a]
  linarith

/-- CK for every Boolean `f` with a coordinate `|\hat f({i})| ≥ a_cut`, at `ρ = tanh ell`,
`ell ≥ 7/2` (via `ck_of_local_cutoff`). -/
theorem ck_of_high_local {n : ℕ} (i : Fin n) (f : Cube n → Bool) {ell : ℝ} (hell : 7/2 ≤ ell)
    (ha : aCut ell ≤ |fourierCoeff (signField f) {i}|) :
    information f (Real.tanh ell) ≤ phi (Real.tanh ell) :=
  ck_of_local_cutoff i f (CenteredSupport.tanh_pos (by linarith)).le (Real.tanh_lt_one ell).le
    aCut_mem.1 ha (local_cutoff hell).le

end MostInformativeBit.HighLocal
