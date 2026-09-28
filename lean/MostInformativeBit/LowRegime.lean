import MostInformativeBit.LocalPropagation
import MostInformativeBit.InfluentialCoordinate
import MostInformativeBit.SingletonCap

/-! Assembly of the small-correlation regime from the actual cube operators,
entropy contraction, singleton cap, and checked scalar inequalities. -/
namespace MostInformativeBit
open scoped BigOperators

@[simp] theorem h_abs (t : ℝ) : h |t| = h t := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos ht, h_neg]

theorem phi_eq_pairF (t : ℝ) : phi t = pairF t := by
  have ht := two_phi_eq_negMulLog t
  simp only [Real.negMulLog] at ht
  unfold pairF
  linarith

theorem phi_quartic_lower {t : ℝ} (ht : |t| ≤ 1) : t^2/2+t^4/12 ≤ phi t := by
  rcases lt_or_eq_of_le ht with hi | hi
  · have hs := sum_le_hasSum (Finset.range 2)
      (fun k _ => by
        apply div_nonneg
        · rw [show 2*k+2 = 2*(k+1) by omega, pow_mul]; positivity
        · positivity) (hasSum_pairF hi)
    rw [← phi_eq_pairF] at hs
    norm_num [Finset.sum_range_succ] at hs
    exact hs
  · have ht' : t = 1 ∨ t = -1 := by simpa only [abs_eq (by norm_num : (0:ℝ) ≤ 1)] using hi
    have hl := LowCertificates.b32.1
    change _ ≤ Real.log 2 at hl
    rcases ht' with rfl | rfl <;> norm_num [phi, h] <;> linarith

theorem phi_quadratic_lower {t : ℝ} (ht : |t| ≤ 1) : t^2/2 ≤ phi t := by
  have hh := phi_quartic_lower ht
  have hp : 0 ≤ t^4 := by positivity
  linarith

theorem phiEntropy_signField {n : ℕ} (f : Cube n → Bool) :
    phiEntropy (signField f) = h (cubeExpect (signField f)) := by
  have hh (x : Cube n) : phi (signField f x) = Real.log 2 := by
    cases hx : f x <;> simp [signField, cubeSign, hx, phi, h]
  unfold phiEntropy
  simp_rw [hh]
  rw [cubeExpect_const]
  unfold phi
  ring

/-- Entropy contraction bounds information by the entropy of the decision bit. -/
theorem information_le_sq_mul_h_mean {n : ℕ} (f : Cube n → Bool) {r : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    information f r ≤ r^2*h (cubeExpect (signField f)) := by
  rw [information_eq_phiEntropy]
  have hc := phiEntropyContraction_holds (by linarith : -1 ≤ r) hr₁
    (signField f) (signField_mem_Icc f)
  rwa [phiEntropy_signField] at hc

/-- The large-mean case from low.tex, including correlation zero. -/
theorem ck_large_mean {n : ℕ} (f : Cube n → Bool) {r : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) (hm : 5/8 ≤ |cubeExpect (signField f)|) :
    information f r ≤ phi r := by
  have hmi := cubeExpect_mem_Icc (signField_mem_Icc f)
  have hma : |cubeExpect (signField f)| ≤ 1 := abs_le.mpr hmi
  have hp := phi_quartic_lower hma
  have hsq : (5/8:ℝ)^2 ≤ cubeExpect (signField f)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5/8) hm 2
  have hfour : (5/8:ℝ)^4 ≤ cubeExpect (signField f)^4 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ (5/8)^2) hsq 2
  have hL := LowCertificates.b32.2
  change Real.log 2 ≤ _ at hL
  have hh : h (cubeExpect (signField f)) ≤ 1/2 := by
    unfold phi at hp
    linarith
  have hi := information_le_sq_mul_h_mean f hr₀ hr₁
  have hs := mul_le_mul_of_nonneg_left hh (sq_nonneg r)
  have hphi := phi_quadratic_lower (abs_le.mpr ⟨by linarith, hr₁⟩)
  linarith

/-- Summing a function over singleton subsets is the coordinate sum. -/
theorem sum_card_one {n : ℕ} (F : Finset (Fin n) → ℝ) :
    (∑ S : Finset (Fin n), if S.card = 1 then F S else 0) = ∑ i, F {i} := by
  classical
  rw [← Finset.sum_filter]
  have hs : (Finset.univ.filter (fun S : Finset (Fin n) => S.card = 1)) =
      Finset.univ.image (fun i : Fin n => ({i} : Finset (Fin n))) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    simpa only [eq_comm] using (Finset.card_eq_one (s := S))
  rw [hs, Finset.sum_image]
  intro a _ b _ hab
  exact Finset.singleton_injective hab

theorem noise_correlation {n : ℕ} (r : ℝ) (v : Cube n → ℝ) :
    cubeExpect (fun x => v x * noise r v x) =
      ∑ S : Finset (Fin n), r^S.card * fourierCoeff v S^2 := by
  rw [fourier_inner]
  simp_rw [fourierCoeff_noise]
  apply Finset.sum_congr rfl
  intro S _
  ring

/-- The exact degree comparison underlying the low-regime Fourier-energy bound. -/
theorem low_fourier_energy {n : ℕ} {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1)
    (v : Cube n → ℝ) :
    -(1-r^2)*cubeExpect v^2 - r^2*(1-r)*(∑ i, fourierCoeff v {i}^2) ≤
      r^2*cubeExpect (fun x => v x*noise r v x) - cubeExpect (fun x => noise r v x^2) := by
  classical
  have hterm (S : Finset (Fin n)) :
      (if S = ∅ then -(1-r^2)*fourierCoeff v S^2 else 0) +
        (if S.card = 1 then -r^2*(1-r)*fourierCoeff v S^2 else 0) ≤
          (r^(S.card+2)-r^(2*S.card))*fourierCoeff v S^2 := by
    by_cases he : S = ∅
    · subst S; simp
    · by_cases hs : S.card = 1
      · simp only [he, hs, ↓reduceIte, zero_add]
        norm_num
        ring_nf
        rfl
      · have hk : 2 ≤ S.card := by
          have hn : S.card ≠ 0 := by simpa using he
          omega
        simp only [he, hs, ↓reduceIte, zero_add]
        exact mul_nonneg (sub_nonneg.mpr (pow_le_pow_of_le_one hr₀ hr₁ (by omega))) (sq_nonneg _)
  have hsum := Finset.sum_le_sum (fun S (_ : S ∈ (Finset.univ : Finset (Finset (Fin n)))) => hterm S)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    fourierCoeff_empty, sum_card_one] at hsum
  rw [noise_correlation, noise_energy]
  calc
    _ = ∑ S : Finset (Fin n), ((if S = ∅ then -(1-r^2)*fourierCoeff v S^2 else 0) +
        (if S.card = 1 then -r^2*(1-r)*fourierCoeff v S^2 else 0)) := by
      simp [Finset.sum_add_distrib, sum_card_one, ← Finset.mul_sum, sub_eq_add_neg, mul_assoc]
    _ ≤ ∑ S : Finset (Fin n), (r^(S.card+2)-r^(2*S.card))*fourierCoeff v S^2 :=
      Finset.sum_le_sum (fun S _ => hterm S)
    _ = _ := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro S _
      rw [pow_add]
      ring

/-- Taking expectations of the actual scalar minorant yields the Fourier-energy bound. -/
theorem low_expected_entropy {n : ℕ} (f : Cube n → Bool) {r : ℝ}
    (hr₀ : 5/8 ≤ r) (hr₁ : r ≤ lowCutoff) :
    lowCoefficient r * (1-r^2-(1-r^2)*cubeExpect (signField f)^2 -
      r^2*(1-r)*(∑ i, fourierCoeff (signField f) {i}^2)) ≤
        cubeExpect (fun x => h (noise r (signField f) x)) := by
  have hr : 0 ≤ r := by linarith
  have hr1 : r ≤ 1 := hr₁.trans low_fixed_facts.cutoff_upper.le
  let u := noise r (signField f)
  have hu (x : Cube n) : u x ∈ Set.Icc (-1) 1 :=
    noise_mem_Icc (by linarith) hr1 (signField_mem_Icc f) x
  have hpoint (x : Cube n) : lowCoefficient r * (1-r^2-u x^2+r^2*|u x|) ≤ h (u x) := by
    have hh := (low_minorant hr₀ hr₁ (abs_nonneg (u x)) (abs_le.mpr (hu x))).2
    rw [h_abs] at hh
    have hp : lowCoefficient r * (1-r^2-u x^2+r^2*|u x|) =
        lowCoefficient r*(1-|u x|)*(1+|u x|-r^2) := by
      rw [← sq_abs (u x)]
      ring
    rw [hp]
    exact hh
  have he := cubeExpect_mono hpoint
  rw [cubeExpect_mul, cubeExpect_add, cubeExpect_sub, cubeExpect_const, cubeExpect_mul] at he
  have hcorr : cubeExpect (fun x => signField f x*u x) ≤ cubeExpect (fun x => |u x|) := by
    apply cubeExpect_mono
    intro x
    cases hx : f x
    · simpa [signField, cubeSign, hx] using neg_le_abs (u x)
    · simpa [signField, cubeSign, hx] using le_abs_self (u x)
  have hegy := low_fourier_energy hr hr1 (signField f)
  change -(1-r^2)*cubeExpect (signField f)^2 - r^2*(1-r)*(∑ i, fourierCoeff (signField f) {i}^2) ≤
    r^2*cubeExpect (fun x => signField f x*u x)-cubeExpect (fun x => u x^2) at hegy
  have hrcorr := mul_le_mul_of_nonneg_left hcorr (sq_nonneg r)
  have hc : 0 < lowCoefficient r := low_coefficient_pos hr₀ hr₁
  have hinner : 1-r^2-(1-r^2)*cubeExpect (signField f)^2 -
      r^2*(1-r)*(∑ i, fourierCoeff (signField f) {i}^2) ≤
      1-r^2-cubeExpect (fun x => u x^2)+r^2*cubeExpect (fun x => |u x|) := by linarith
  exact (mul_le_mul_of_nonneg_left hinner hc.le).trans he

/-- The mean credit in low.tex, using the actual balanced lift and finite Fourier energy. -/
theorem low_credit {n : ℕ} (f : Cube n → Bool) {r : ℝ}
    (hr₀ : 5/8 ≤ r) (hr₁ : r ≤ lowCutoff)
    (ha : ∀ i, |fourierCoeff (signField f) {i}| ≤ 5/8)
    (hm : |cubeExpect (signField f)| ≤ 5/8) :
    lowCoefficient r*(1-r)*(1+r-(49:ℝ)/64*r^2) +
      (1/2-lowCoefficient r*(1-2*r^2+r^3))*cubeExpect (signField f)^2 ≤
        cubeExpect (fun x => h (noise r (signField f) x)) + phi (cubeExpect (signField f)) := by
  have he := low_expected_entropy f hr₀ hr₁
  have hcap := SingletonCap.balanced_lift f ha hm
  have hp := phi_quadratic_lower (hm.trans (by norm_num : (5/8:ℝ) ≤ 1))
  have hnon : 0 ≤ lowCoefficient r*r^2*(1-r) :=
    mul_nonneg (mul_nonneg (low_coefficient_pos hr₀ hr₁).le (sq_nonneg r))
      (sub_nonneg.mpr (hr₁.trans low_fixed_facts.cutoff_upper.le))
  have hh := mul_le_mul_of_nonneg_left hcap hnon
  nlinarith

/-- The intermediate-correlation, small-coefficient case. -/
theorem ck_low_small_coefficients {n : ℕ} (f : Cube n → Bool) {r : ℝ}
    (hr₀ : 5/8 ≤ r) (hr₁ : r ≤ lowCutoff)
    (ha : ∀ i, |fourierCoeff (signField f) {i}| ≤ 5/8)
    (hm : |cubeExpect (signField f)| ≤ 5/8) : information f r ≤ phi r := by
  have hc := low_credit f hr₀ hr₁ ha hm
  have hb := low_scalar_bound hr₀ hr₁
  have hn := mul_nonneg (low_mean_coefficient_nonneg hr₀ (hr₁.trans low_fixed_facts.cutoff_upper.le))
    (sq_nonneg (cubeExpect (signField f)))
  rw [information_eq_phiEntropy]
  unfold phiEntropy
  rw [cubeExpect_noise]
  unfold phi
  rw [cubeExpect_sub, cubeExpect_const]
  unfold phi at hc
  linarith

/-- Starting slack at 5/8 gives the stronger quadratic bound for the small case. -/
theorem information_start_small {n : ℕ} (f : Cube n → Bool)
    (ha : ∀ i, |fourierCoeff (signField f) {i}| ≤ 5/8)
    (hm : |cubeExpect (signField f)| ≤ 5/8) : information f (5/8) ≤ (5/8:ℝ)^2/2 := by
  have hcut : (5/8:ℝ) ≤ lowCutoff := by linarith [low_fixed_facts.cutoff_lower]
  have hc := low_credit f le_rfl hcut ha hm
  have hs := low_fixed_facts.starting_slack
  have hn := mul_nonneg (low_mean_coefficient_nonneg (r := 5/8) le_rfl (by norm_num))
    (sq_nonneg (cubeExpect (signField f)))
  rw [information_eq_phiEntropy]
  unfold phiEntropy
  rw [cubeExpect_noise]
  unfold phi
  rw [cubeExpect_sub, cubeExpect_const]
  unfold phi at hc
  linarith

/-- Entropy contraction combined with the exact noise semigroup. -/
theorem information_rescale {n : ℕ} (f : Cube n → Bool) {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) (hs₀ : 0 < s) (hs₁ : s ≤ 1) :
    information f r ≤ (r/s)^2 * information f s := by
  have hratio₀ : -1 ≤ r/s := le_trans (by norm_num) (div_nonneg hr hs₀.le)
  have hratio₁ : r/s ≤ 1 := (div_le_one hs₀).mpr hrs
  have hc := phiEntropyContraction_holds hratio₀ hratio₁ (noise s (signField f))
    (noise_mem_Icc (by linarith) hs₁ (signField_mem_Icc f))
  rw [noise_comp, div_mul_cancel₀ r hs₀.ne'] at hc
  simpa only [information_eq_phiEntropy] using hc

/-- The small-coefficient case extends down to zero by the starting slack. -/
theorem ck_below_start_small {n : ℕ} (f : Cube n → Bool) {r : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 5/8)
    (ha : ∀ i, |fourierCoeff (signField f) {i}| ≤ 5/8)
    (hm : |cubeExpect (signField f)| ≤ 5/8) : information f r ≤ phi r := by
  have hc := information_rescale f hr₀ hr₁ (by norm_num : (0:ℝ) < 5/8) (by norm_num)
  have hs := mul_le_mul_of_nonneg_left (information_start_small f ha hm) (sq_nonneg (r/(5/8)))
  have hp := phi_quadratic_lower (t := r) (abs_le.mpr ⟨by linarith, by linarith⟩)
  norm_num at hc hs
  nlinarith

/-- The large-singleton branch throughout the full low-correlation range. -/
theorem ck_low_large_singleton {n : ℕ} (f : Cube n → Bool) (i : Fin n) {r : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ lowCutoff)
    (ha : 5/8 ≤ |fourierCoeff (signField f) {i}|) : information f r ≤ phi r := by
  apply ck_of_local_cutoff i f hr₀ (hr₁.trans low_fixed_facts.cutoff_upper.le)
    (by norm_num : (0:ℝ) ≤ 5/8) ha
  exact low_local_criterion hr₀ hr₁ le_rfl (by norm_num)

/-- The unconditional small-correlation theorem, including the zero-dimensional cube. -/
theorem ck_low {n : ℕ} (f : Cube n → Bool) {r : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ lowCutoff) : information f r ≤ phi r := by
  by_cases hm : 5/8 ≤ |cubeExpect (signField f)|
  · exact ck_large_mean f hr₀ (hr₁.trans low_fixed_facts.cutoff_upper.le) hm
  · have hm' : |cubeExpect (signField f)| ≤ 5/8 := (lt_of_not_ge hm).le
    by_cases ha : ∃ i, 5/8 ≤ |fourierCoeff (signField f) {i}|
    · obtain ⟨i, hi⟩ := ha
      exact ck_low_large_singleton f i hr₀ hr₁ hi
    · have ha' : ∀ i, |fourierCoeff (signField f) {i}| ≤ 5/8 := by
        intro i
        exact (lt_of_not_ge (fun hi => ha ⟨i, hi⟩)).le
      rcases le_total (5/8) r with hr | hr
      · exact ck_low_small_coefficients f hr hr₁ ha' hm'
      · exact ck_below_start_small f hr₀ hr ha' hm'

end MostInformativeBit
