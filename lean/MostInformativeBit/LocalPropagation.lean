import MostInformativeBit.LowScalar
import MostInformativeBit.InfluentialCoordinate
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Local cutoff margins. Concavity propagates any checked margin upward in
its singleton coefficient. The low cutoff is certified uniformly in correlation
by an explicit finite lower polynomial with a proved nonnegative series tail. -/
namespace MostInformativeBit
open scoped BigOperators

noncomputable def localMargin (r a : ℝ) : ℝ := (1-r^2)*h (r*a) - (1-a*r^2)*h r

@[simp] theorem localMargin_one (r : ℝ) : localMargin r 1 = 0 := by simp [localMargin]
@[simp] theorem localMargin_zero (a : ℝ) : localMargin 0 a = 0 := by simp [localMargin]

theorem h_concaveOn : ConcaveOn ℝ (Set.Icc (-1) 1) h := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hp := phi_convexOn.2 hx hy ha hb hab
  simp only [smul_eq_mul, phi] at hp ⊢
  have hL : a*Real.log 2+b*Real.log 2 = Real.log 2 := by rw [← add_mul, hab, one_mul]
  linarith

theorem localMargin_concaveOn {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    ConcaveOn ℝ (Set.Icc (0:ℝ) 1) (localMargin r) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : r*x ∈ Set.Icc (-1) 1 := by constructor <;> nlinarith [hx.1, hx.2]
  have hy' : r*y ∈ Set.Icc (-1) 1 := by constructor <;> nlinarith [hy.1, hy.2]
  have hh := h_concaveOn.2 hx' hy' ha hb hab
  simp only [smul_eq_mul] at hh ⊢
  have hd : 0 ≤ 1-r^2 := by nlinarith
  have hc := mul_le_mul_of_nonneg_left hh hd
  have he : a*(r*x)+b*(r*y) = r*(a*x+b*y) := by ring
  rw [he] at hc
  unfold localMargin
  have hR : a*h r+b*h r = h r := by rw [← add_mul, hab, one_mul]
  nlinarith

/-- Generic propagation in the singleton coefficient, used by every channel range. -/
theorem localMargin_nonneg_above {r a₀ a : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1)
    (ha₀ : 0 ≤ a₀) (haa : a₀ ≤ a) (ha₁ : a ≤ 1) (hm : 0 ≤ localMargin r a₀) :
    0 ≤ localMargin r a := by
  by_cases h0 : a₀ = 1
  · have ha : a = 1 := by linarith
    simp [ha]
  · have hpos : 0 < 1-a₀ := sub_pos.mpr (lt_of_le_of_ne (haa.trans ha₁) h0)
    let t := (1-a)/(1-a₀)
    have ht₀ : 0 ≤ t := div_nonneg (sub_nonneg.mpr ha₁) hpos.le
    have ht₁ : t ≤ 1 := (div_le_one hpos).mpr (by linarith)
    have he : t*a₀+(1-t)*1 = a := by dsimp [t]; field_simp; ring
    have hc := (localMargin_concaveOn hr₀ hr₁).2
      (show a₀ ∈ Set.Icc (0:ℝ) 1 from ⟨ha₀, haa.trans ha₁⟩)
      (show (1:ℝ) ∈ Set.Icc (0:ℝ) 1 from ⟨zero_le_one, le_rfl⟩)
      ht₀ (sub_nonneg.mpr ht₁) (by ring : t+(1-t)=1)
    simp only [smul_eq_mul, he, localMargin_one, mul_zero, add_zero] at hc
    exact (mul_nonneg ht₀ hm).trans hc

/-- An endpoint margin and a large singleton coefficient imply CK, uniformly in dimension. -/
theorem ck_of_local_cutoff {n : ℕ} (i : Fin n) (f : Cube n → Bool) {r a₀ : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) (ha₀ : 0 ≤ a₀)
    (ha : a₀ ≤ |fourierCoeff (signField f) {i}|) (hm : 0 ≤ localMargin r a₀) :
    information f r ≤ phi r := by
  have hbound := mean_abs_add_singleton_abs_le_one i (signField_mem_Icc f)
  have hle : |fourierCoeff (signField f) {i}| ≤ 1 :=
    (le_add_of_nonneg_left (abs_nonneg (cubeExpect (signField f)))).trans hbound
  have hmargin := localMargin_nonneg_above hr₀ hr₁ ha₀ ha hle hm
  apply ck_of_S8 i f hr₀ hr₁
  simpa only [localMargin, mul_comm (r^2) _] using hmargin

namespace LocalPropagation

noncomputable def c (k : ℕ) : ℝ := 1 / ((2*(k:ℝ)+1)*(2*(k:ℝ)+2))
noncomputable def a : ℝ := 5/8
noncomputable def d (k : ℕ) : ℝ :=
  c k*(1-a^(2*k+2)) - if k=0 then 0 else c (k-1)*(a-a^(2*k))
noncomputable def upperSquare : ℝ := (457/500:ℝ)^2
noncomputable def logUpper : ℝ := 693147180560/1000000000000
noncomputable def lowerPolynomial (t : ℝ) : ℝ :=
  (∑ k ∈ Finset.range 8, d k*t^k) - (1-a)*logUpper
noncomputable def lowerDerivative (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 8, d k*(k:ℝ)*t^(k-1)

private theorem phi_pairF (t : ℝ) : phi t = pairF t := by
  have ht := two_phi_eq_negMulLog t
  simp only [Real.negMulLog] at ht
  unfold pairF
  linarith

theorem hasSum_phi_coeff {r : ℝ} (hr : |r| < 1) :
    HasSum (fun k : ℕ => c k*r^(2*k+2)) (phi r) := by
  rw [phi_pairF]
  convert hasSum_pairF hr using 1
  ext k
  simp [c, div_eq_mul_inv, mul_comm]

/-- The shifted entropy series has nonnegative tail beyond the eighth term. -/
theorem d_nonneg_tail {k : ℕ} (hk : 8 ≤ k) : 0 ≤ d k := by
  have hk0 : k ≠ 0 := by omega
  have hkr : (8:ℝ) ≤ k := by exact_mod_cast hk
  have hkcast : ((k-1:ℕ):ℝ) = (k:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hD₀ : 0 < (2*(k:ℝ)-1)*(2*(k:ℝ)) := mul_pos (by linarith) (by linarith)
  have hD₁ : 0 < (2*(k:ℝ)+1)*(2*(k:ℝ)+2) := by positivity
  have hbase : 0 ≤ (2*(k:ℝ)-1)*(2*(k:ℝ)) - a*((2*(k:ℝ)+1)*(2*(k:ℝ)+2)) := by
    unfold a
    nlinarith [sq_nonneg ((k:ℝ)-8)]
  have hfac : 0 ≤ (2*(k:ℝ)+1)*(2*(k:ℝ)+2) - a^2*((2*(k:ℝ)-1)*(2*(k:ℝ))) := by
    unfold a
    nlinarith [sq_nonneg (k:ℝ)]
  have hp : 0 ≤ a^(2*k) := by unfold a; positivity
  have hid : d k =
      ((2*(k:ℝ)-1)*(2*(k:ℝ)) - a*((2*(k:ℝ)+1)*(2*(k:ℝ)+2)) +
        a^(2*k)*((2*(k:ℝ)+1)*(2*(k:ℝ)+2) - a^2*((2*(k:ℝ)-1)*(2*(k:ℝ))))) /
      (((2*(k:ℝ)+1)*(2*(k:ℝ)+2))*((2*(k:ℝ)-1)*(2*(k:ℝ)))) := by
    unfold d c
    rw [if_neg hk0, hkcast, pow_add]
    rw [show 2*((k:ℝ)-1)+1 = 2*(k:ℝ)-1 by ring,
      show 2*((k:ℝ)-1)+2 = 2*(k:ℝ) by ring]
    have hkR : (k:ℝ) ≠ 0 := by linarith
    have hkR1 : 2*(k:ℝ)-1 ≠ 0 := by linarith
    field_simp [hkR, hkR1]
    ring
  rw [hid]
  exact div_nonneg (add_nonneg hbase (mul_nonneg hp hfac)) (mul_pos hD₁ hD₀).le

/-- A direct power-series representation of the fixed 5/8 local margin. -/
theorem hasSum_margin {r : ℝ} (hr : |r| < 1) :
    HasSum (fun k : ℕ => d k*r^(2*k+2)) (localMargin r a + r^2*(1-a)*Real.log 2) := by
  have har : |a*r| < 1 := by
    rw [abs_mul]
    norm_num [a]
    nlinarith [abs_nonneg r]
  have h₀ := hasSum_phi_coeff hr
  have h₁ := hasSum_phi_coeff har
  have hA := h₀.sub h₁
  have hB := ((h₀.mul_left a).sub h₁).mul_left (r^2)
  let b : ℕ → ℝ := fun k => if k=0 then 0 else c (k-1)*(a-a^(2*k))*r^(2*k+2)
  have hbs : HasSum (fun k => b (k+1)) (r^2*(a*phi r-phi (a*r))) := by
    have he : (fun k => b (k+1)) =
        (fun k => r^2*(a*(c k*r^(2*k+2))-c k*(a*r)^(2*k+2))) := by
      ext k
      simp only [b, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
        Nat.add_sub_cancel, mul_pow]
      rw [show 2*(k+1)+2 = (2*k+2)+2 by omega, pow_add,
        show 2*(k+1) = 2*k+2 by omega]
      ring
    rw [he]
    exact hB
  have hb : HasSum b (r^2*(a*phi r-phi (a*r))) := by
    simpa only [b, ↓reduceIte, zero_add] using hbs.zero_add
  have hs := hA.sub hb
  have hfun : (fun k => d k*r^(2*k+2)) =
      (fun k => c k*r^(2*k+2)-c k*(a*r)^(2*k+2)-b k) := by
    ext k
    simp only [d, b, mul_pow]
    split_ifs <;> ring
  have htotal : localMargin r a+r^2*(1-a)*Real.log 2 =
      phi r-phi (a*r)-r^2*(a*phi r-phi (a*r)) := by
    unfold localMargin phi
    rw [mul_comm a r]
    ring
  rw [hfun, htotal]
  exact hs

theorem lowerPolynomial_hasDerivAt (t : ℝ) :
    HasDerivAt lowerPolynomial (lowerDerivative t) t := by
  unfold lowerPolynomial lowerDerivative
  convert (show HasDerivAt (fun x : ℝ =>
    (∑ k ∈ Finset.range 8, d k*x^k) - (1-a)*logUpper)
    ((∑ k ∈ Finset.range 8, d k*(k*t^(k-1)))) t from
    (HasDerivAt.fun_sum (fun k (_ : k ∈ Finset.range 8) =>
      (hasDerivAt_pow k t).const_mul (d k))).sub_const ((1-a)*logUpper)) using 1
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem lowerDerivative_nonpos {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ upperSquare) :
    lowerDerivative t ≤ 0 := by
  have h₃ := pow_le_pow_left₀ ht₀ ht₁ 3
  have h₄ := pow_le_pow_left₀ ht₀ ht₁ 4
  have h₅ := pow_le_pow_left₀ ht₀ ht₁ 5
  have h₆ := pow_le_pow_left₀ ht₀ ht₁ 6
  norm_num [lowerDerivative, Finset.sum_range_succ, d, c, a, upperSquare] at *
  nlinarith [sq_nonneg t]

theorem lowerPolynomial_pos {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ upperSquare) :
    0 < lowerPolynomial t := by
  have hmono : AntitoneOn lowerPolynomial (Set.Icc 0 upperSquare) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · apply Continuous.continuousOn
      unfold lowerPolynomial
      fun_prop
    · intro x _
      exact (lowerPolynomial_hasDerivAt x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(lowerPolynomial_hasDerivAt x).deriv]
      exact lowerDerivative_nonpos (interior_subset hx).1 (interior_subset hx).2
  have hend : 0 < lowerPolynomial upperSquare := by
    norm_num [lowerPolynomial, upperSquare, logUpper, Finset.sum_range_succ, d, c, a]
  exact hend.trans_le (hmono ⟨ht₀, ht₁⟩ ⟨by norm_num [upperSquare], le_rfl⟩ ht₁)

theorem margin_nonneg {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 457/500) :
    0 ≤ localMargin r (5/8) := by
  have habs : |r| < 1 := by rw [abs_of_nonneg hr₀]; linarith
  have hs := sum_le_hasSum (Finset.range 8)
    (fun k hk => mul_nonneg (d_nonneg_tail (by simpa using hk)) (pow_nonneg hr₀ _))
    (hasSum_margin habs)
  have hL : Real.log 2 ≤ logUpper := by
    have he := LowCertificates.b32.2
    change Real.log 2 ≤ _ at he
    unfold logUpper
    linarith
  have ht : r^2 ≤ upperSquare := pow_le_pow_left₀ hr₀ hr₁ 2
  have hp := (lowerPolynomial_pos (sq_nonneg r) ht).le
  have hmul := mul_nonneg (sq_nonneg r) hp
  have hlog := mul_le_mul_of_nonneg_left hL
    (show 0 ≤ r^2*(1-a) by unfold a; positivity)
  have he : (∑ k ∈ Finset.range 8, d k*r^(2*k+2)) =
      r^2*(lowerPolynomial (r^2)+(1-a)*logUpper) := by
    simp only [lowerPolynomial, sub_add_cancel, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_add, ← pow_mul]
    ring
  rw [he] at hs
  change 0 ≤ localMargin r a
  nlinarith

end LocalPropagation

/-- The low-regime local criterion, uniformly on a slightly larger rational interval. -/
theorem low_local_criterion {r a : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ lowCutoff)
    (ha₀ : 5/8 ≤ a) (ha₁ : a ≤ 1) : 0 ≤ localMargin r a := by
  have hr : r ≤ 457/500 := by
    have hc := LowCertificates.b7.2
    change lowCutoff ≤ _ at hc
    linarith
  exact localMargin_nonneg_above hr₀ (by linarith) (by norm_num) ha₀ ha₁
    (LocalPropagation.margin_nonneg hr₀ hr)

end MostInformativeBit
