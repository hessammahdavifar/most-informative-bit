import MostInformativeBit.MonotoneReduction
import MostInformativeBit.EntropyTensorization
import MostInformativeBit.MeanCorrection

/-! The influential-coordinate inequality (S6) and CK criterion (S8), using
the proved entropy contraction and mean correction. -/
namespace MostInformativeBit
open scoped BigOperators

/-- Keep a selected input bit fixed; the field still lives on the same cube. -/
def cubeSection {n : ℕ} {α : Type*} (i : Fin n) (v : Cube n → α) (b : Bool) : Cube n → α :=
  fun x => v (Function.update x i b)

/-- Noise only bit `i`, in the paper's correlation parametrization. -/
noncomputable def bitNoise {n : ℕ} (i : Fin n) (r : ℝ) (v : Cube n → ℝ) (x : Cube n) : ℝ :=
  ((1+r)/2) * v x + ((1-r)/2) * v (cubeFlip i x)

theorem cubeFlip_update {n : ℕ} (i : Fin n) (x : Cube n) (b : Bool) :
    cubeFlip i (Function.update x i b) = Function.update x i (!b) := by
  simp [cubeFlip, Function.update_idem]

theorem bitNoise_section {n : ℕ} (i : Fin n) (r : ℝ) (v : Cube n → ℝ) (b : Bool) :
    cubeSection i (bitNoise i r v) b = fun x =>
      ((1+r)/2) * cubeSection i v b x + ((1-r)/2) * cubeSection i v (!b) x := by
  ext x
  simp only [cubeSection, bitNoise, cubeFlip_update]

@[simp] theorem sectionNoise_cubeSection {n : ℕ} (i : Fin n) (r : ℝ) (v : Cube n → ℝ)
    (y : Cube n) (b c : Bool) : sectionNoise i r (cubeSection i v b) y c = sectionNoise i r v y b := by
  simp only [sectionNoise, cubeSection, Function.update_idem]

theorem noise_cubeSection {n : ℕ} (i : Fin n) (r : ℝ) (v : Cube n → ℝ) (b : Bool) (y : Cube n) :
    noise r (cubeSection i v b) y = sectionNoise i r v y b := by
  have hn := noise_section i r (cubeSection i v b) y (y i)
  rw [Function.update_eq_self] at hn
  simp only [sectionNoise_cubeSection] at hn
  linarith

/-- Noising a section after the chosen bit gives the corresponding full-noise section. -/
theorem noise_bitNoise_section {n : ℕ} (i : Fin n) (r : ℝ) (v : Cube n → ℝ) (b : Bool) (y : Cube n) :
    noise r (cubeSection i (bitNoise i r v) b) y = noise r v (Function.update y i b) := by
  rw [bitNoise_section, noise_add, noise_mul, noise_mul]
  simp only [noise_cubeSection, noise_section]

theorem cubeExpect_bitNoise {n : ℕ} (i : Fin n) (r : ℝ) (v : Cube n → ℝ) :
    cubeExpect (bitNoise i r v) = cubeExpect v := by
  unfold bitNoise
  rw [cubeExpect_add, cubeExpect_mul, cubeExpect_mul, cubeExpect_flip]
  ring

/-- The two section means sum to twice the full mean. -/
theorem cubeExpect_sections_sum {n : ℕ} (i : Fin n) (v : Cube n → ℝ) :
    cubeExpect (cubeSection i v false) + cubeExpect (cubeSection i v true) = 2*cubeExpect v := by
  rw [← cubeExpect_add]
  exact cubeExpect_update_pair i v

/-- The two section means differ by twice the singleton coefficient. -/
theorem cubeExpect_sections_sub {n : ℕ} (i : Fin n) (v : Cube n → ℝ) :
    cubeExpect (cubeSection i v true) - cubeExpect (cubeSection i v false) =
      2*fourierCoeff v {i} := by
  let w : Cube n → ℝ := fun x => v x * character {i} x
  have hp (x : Cube n) : cubeSection i v true x - cubeSection i v false x = w x + w (cubeFlip i x) := by
    cases hx : x i
    · have hx₀ : Function.update x i false = x := by
        simpa only [hx] using Function.update_eq_self i x
      simp [cubeSection, w, character, cubeSign, cubeFlip, hx, hx₀]
      ring
    · have hx₁ : Function.update x i true = x := by
        simpa only [hx] using Function.update_eq_self i x
      simp [cubeSection, w, character, cubeSign, cubeFlip, hx, hx₁]
      ring
  rw [← cubeExpect_sub]
  simp_rw [hp]
  rw [cubeExpect_add, cubeExpect_flip]
  change cubeExpect w + cubeExpect w = 2*cubeExpect w
  ring

theorem cubeExpect_section_false {n : ℕ} (i : Fin n) (v : Cube n → ℝ) :
    cubeExpect (cubeSection i v false) = cubeExpect v - fourierCoeff v {i} := by
  linarith [cubeExpect_sections_sum i v, cubeExpect_sections_sub i v]

theorem cubeExpect_section_true {n : ℕ} (i : Fin n) (v : Cube n → ℝ) :
    cubeExpect (cubeSection i v true) = cubeExpect v + fourierCoeff v {i} := by
  linarith [cubeExpect_sections_sum i v, cubeExpect_sections_sub i v]

theorem cubeExpect_bitNoise_section_false {n : ℕ} (i : Fin n) (r : ℝ) (v : Cube n → ℝ) :
    cubeExpect (cubeSection i (bitNoise i r v) false) = cubeExpect v - r*fourierCoeff v {i} := by
  rw [bitNoise_section, cubeExpect_add, cubeExpect_mul, cubeExpect_mul]
  simp only [Bool.not_false, cubeExpect_section_false, cubeExpect_section_true]
  ring

theorem cubeExpect_bitNoise_section_true {n : ℕ} (i : Fin n) (r : ℝ) (v : Cube n → ℝ) :
    cubeExpect (cubeSection i (bitNoise i r v) true) = cubeExpect v + r*fourierCoeff v {i} := by
  rw [bitNoise_section, cubeExpect_add, cubeExpect_mul, cubeExpect_mul]
  simp only [Bool.not_true, cubeExpect_section_false, cubeExpect_section_true]
  ring

theorem bitNoise_mem_Icc {n : ℕ} (i : Fin n) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1)
    {v : Cube n → ℝ} (hv : ∀ x, v x ∈ Set.Icc (-1) 1) (x : Cube n) :
    bitNoise i r v x ∈ Set.Icc (-1) 1 := by
  have h₀ := hv x
  have h₁ := hv (cubeFlip i x)
  have ha : 0 ≤ (1+r)/2 := by linarith
  have hb : 0 ≤ (1-r)/2 := by linarith
  constructor <;> unfold bitNoise
  · nlinarith [mul_nonneg ha (by linarith [h₀.1] : 0 ≤ v x+1),
      mul_nonneg hb (by linarith [h₁.1] : 0 ≤ v (cubeFlip i x)+1)]
  · nlinarith [mul_nonneg ha (by linarith [h₀.2] : 0 ≤ 1-v x),
      mul_nonneg hb (by linarith [h₁.2] : 0 ≤ 1-v (cubeFlip i x))]

/-- The sign mean and a singleton coefficient obey the full scalar S7 domain. -/
theorem mean_abs_add_singleton_abs_le_one {n : ℕ} (i : Fin n) {v : Cube n → ℝ}
    (hv : ∀ x, v x ∈ Set.Icc (-1) 1) : |cubeExpect v| + |fourierCoeff v {i}| ≤ 1 := by
  have h₀ := cubeExpect_mem_Icc (fun x => hv (Function.update x i false))
  have h₁ := cubeExpect_mem_Icc (fun x => hv (Function.update x i true))
  change cubeExpect (cubeSection i v false) ∈ Set.Icc (-1) 1 at h₀
  change cubeExpect (cubeSection i v true) ∈ Set.Icc (-1) 1 at h₁
  rw [cubeExpect_section_false] at h₀
  rw [cubeExpect_section_true] at h₁
  rcases le_total 0 (cubeExpect v) with hm | hm <;>
    rcases le_total 0 (fourierCoeff v {i}) with ha | ha
  · rw [abs_of_nonneg hm, abs_of_nonneg ha]; exact h₁.2
  · rw [abs_of_nonneg hm, abs_of_nonpos ha]; linarith [h₀.2]
  · rw [abs_of_nonpos hm, abs_of_nonneg ha]; linarith [h₀.1]
  · rw [abs_of_nonpos hm, abs_of_nonpos ha]; linarith [h₁.1]

@[simp] theorem h_neg (t : ℝ) : h (-t) = h t := by
  unfold h
  rw [show (1- -t)/2 = 1-(1-t)/2 by ring, Real.binEntropy_one_sub]

@[simp] theorem h_one : h 1 = 0 := by simp [h]

theorem h_nonneg {t : ℝ} (ht₀ : -1 ≤ t) (ht₁ : t ≤ 1) : 0 ≤ h t := by
  exact Real.binEntropy_nonneg (by linarith) (by linarith)

/-- Pivotal-edge indicator, constant along each chosen-coordinate edge. -/
def pivotalIndicator {n : ℕ} (i : Fin n) (f : Cube n → Bool) (x : Cube n) : ℝ :=
  if f (Function.update x i false) = f (Function.update x i true) then 0 else 1

noncomputable def pivotalProbability {n : ℕ} (i : Fin n) (f : Cube n → Bool) : ℝ :=
  cubeExpect (pivotalIndicator i f)

theorem pivotalIndicator_eq_flip {n : ℕ} (i : Fin n) (f : Cube n → Bool) (x : Cube n) :
    pivotalIndicator i f x = if f x = f (cubeFlip i x) then 0 else 1 := by
  cases hx : x i
  · have hx₀ : Function.update x i false = x := by
      simpa only [hx] using Function.update_eq_self i x
    simp [pivotalIndicator, cubeFlip, hx, hx₀]
  · have hx₁ : Function.update x i true = x := by
      simpa only [hx] using Function.update_eq_self i x
    simp [pivotalIndicator, cubeFlip, hx, hx₁, eq_comm]

theorem singleton_abs_le_pivotalProbability {n : ℕ} (i : Fin n) (f : Cube n → Bool) :
    |fourierCoeff (signField f) {i}| ≤ pivotalProbability i f := by
  let d : Cube n → ℝ := fun x =>
    (signField f (Function.update x i true) - signField f (Function.update x i false))/2
  have hd : cubeExpect d = fourierCoeff (signField f) {i} := by
    have he := cubeExpect_sections_sub i (signField f)
    dsimp [d]
    simp only [div_eq_mul_inv]
    have hh : (fun x => (signField f (Function.update x i true) -
        signField f (Function.update x i false)) * (2:ℝ)⁻¹) =
        fun x => (2:ℝ)⁻¹ * (cubeSection i (signField f) true x -
          cubeSection i (signField f) false x) := by ext x; dsimp [cubeSection]; ring
    rw [hh, cubeExpect_mul, cubeExpect_sub]
    linarith
  have hb (x : Cube n) : -pivotalIndicator i f x ≤ d x ∧ d x ≤ pivotalIndicator i f x := by
    cases h₀ : f (Function.update x i false) <;> cases h₁ : f (Function.update x i true) <;>
      norm_num [d, signField, cubeSign, pivotalIndicator, h₀, h₁]
  have hu := cubeExpect_mono (fun x => (hb x).2)
  have hl := cubeExpect_mono (fun x => (hb x).1)
  rw [hd] at hu hl
  have hn : cubeExpect (fun x => -pivotalIndicator i f x) = -pivotalProbability i f := by
    simp [cubeExpect, pivotalProbability, Finset.sum_neg_distrib]
  rw [hn] at hl
  exact abs_le.mpr ⟨hl, hu⟩

theorem h_bool_mix (a b : Bool) (r : ℝ) :
    h (((1+r)/2)*cubeSign a + ((1-r)/2)*cubeSign b) = if a = b then 0 else h r := by
  cases a <;> cases b <;> simp only [cubeSign, Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte] <;> ring_nf <;> simp

/-- Only pivotal edges contribute entropy after noising one bit. -/
theorem h_bitNoise_signField {n : ℕ} (i : Fin n) (f : Cube n → Bool) (r : ℝ) (x : Cube n) :
    h (bitNoise i r (signField f) x) = pivotalIndicator i f x * h r := by
  simp only [bitNoise, signField, h_bool_mix, pivotalIndicator_eq_flip]
  split_ifs <;> simp

theorem cubeExpect_h_bitNoise {n : ℕ} (i : Fin n) (f : Cube n → Bool) (r : ℝ) :
    cubeExpect (fun x => h (bitNoise i r (signField f) x)) = pivotalProbability i f * h r := by
  simp_rw [h_bitNoise_signField]
  simp only [cubeExpect, pivotalProbability, ← Finset.sum_mul, mul_assoc]

/-- The proved phi-entropy contraction, expressed in the paper's h convention. -/
theorem h_noise_lower {n : ℕ} {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1)
    {v : Cube n → ℝ} (hv : ∀ x, v x ∈ Set.Icc (-1) 1) :
    r^2*cubeExpect (fun x => h (v x)) + (1-r^2)*h (cubeExpect v) ≤
      cubeExpect (fun x => h (noise r v x)) := by
  have he := phiEntropyContraction_holds (by linarith : -1 ≤ r) hr₁ v hv
  unfold phiEntropy phi at he
  rw [cubeExpect_sub, cubeExpect_sub, cubeExpect_const, cubeExpect_noise] at he
  nlinarith

/-- Applying entropy contraction after noising the chosen bit first. -/
theorem influential_section_entropy {n : ℕ} (i : Fin n) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1)
    {v : Cube n → ℝ} (hv : ∀ x, v x ∈ Set.Icc (-1) 1) :
    r^2*cubeExpect (fun x => h (bitNoise i r v x)) +
      (1-r^2)/2 * (h (cubeExpect v+r*fourierCoeff v {i}) +
        h (cubeExpect v-r*fourierCoeff v {i})) ≤ cubeExpect (fun x => h (noise r v x)) := by
  have h₀ := h_noise_lower hr₀ hr₁ (fun x => bitNoise_mem_Icc i hr₀ hr₁ hv (Function.update x i false))
  have h₁ := h_noise_lower hr₀ hr₁ (fun x => bitNoise_mem_Icc i hr₀ hr₁ hv (Function.update x i true))
  change r^2*cubeExpect (fun x => h (cubeSection i (bitNoise i r v) false x)) +
    (1-r^2)*h (cubeExpect (cubeSection i (bitNoise i r v) false)) ≤
      cubeExpect (fun x => h (noise r (cubeSection i (bitNoise i r v) false) x)) at h₀
  change r^2*cubeExpect (fun x => h (cubeSection i (bitNoise i r v) true x)) +
    (1-r^2)*h (cubeExpect (cubeSection i (bitNoise i r v) true)) ≤
      cubeExpect (fun x => h (noise r (cubeSection i (bitNoise i r v) true) x)) at h₁
  simp only [noise_bitNoise_section, cubeExpect_bitNoise_section_false,
    cubeExpect_bitNoise_section_true] at h₀ h₁
  have hs := cubeExpect_sections_sum i (fun x => h (bitNoise i r v x))
  have hn := cubeExpect_sections_sum i (fun x => h (noise r v x))
  change cubeExpect (fun x => h (cubeSection i (bitNoise i r v) false x)) +
    cubeExpect (fun x => h (cubeSection i (bitNoise i r v) true x)) =
      2*cubeExpect (fun x => h (bitNoise i r v x)) at hs
  change cubeExpect (fun x => h (noise r v (Function.update x i false))) +
    cubeExpect (fun x => h (noise r v (Function.update x i true))) =
      2*cubeExpect (fun x => h (noise r v x)) at hn
  nlinarith [congrArg (fun t : ℝ => r^2*t) hs]

/-- The sum of the section entropies is insensitive to the sign of the coefficient. -/
theorem h_pair_abs (m r a : ℝ) :
    h (m+r*|a|) + h (m-r*|a|) = h (m+r*a) + h (m-r*a) := by
  rcases le_total 0 a with ha | ha
  · rw [abs_of_nonneg ha]
  · simp only [abs_of_nonpos ha, mul_neg, sub_eq_add_neg, neg_neg]
    exact add_comm _ _

/-- The manuscript's influential-coordinate inequality (S6), with no monotonicity assumption. -/
theorem S6 {n : ℕ} (i : Fin n) (f : Cube n → Bool) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    r^2 * |fourierCoeff (signField f) {i}| * h r +
      (1-r^2)/2 * (h (cubeExpect (signField f)+r*|fourierCoeff (signField f) {i}|) +
        h (cubeExpect (signField f)-r*|fourierCoeff (signField f) {i}|)) ≤
      cubeExpect (fun x => h (noise r (signField f) x)) := by
  have he := influential_section_entropy i hr₀ hr₁ (signField_mem_Icc f)
  rw [cubeExpect_h_bitNoise] at he
  rw [h_pair_abs]
  have hp := singleton_abs_le_pivotalProbability i f
  have hn : 0 ≤ r^2 * h r := mul_nonneg (sq_nonneg r) (h_nonneg (by linarith) hr₁)
  have hm := mul_le_mul_of_nonneg_right hp hn
  nlinarith

/-- S6 and the proved mean correction bound information by a single Fourier coefficient. -/
theorem information_influential_upper {n : ℕ} (i : Fin n) (f : Cube n → Bool)
    {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    information f r ≤ Real.log 2 - r^2*|fourierCoeff (signField f) {i}| * h r -
      (1-r^2)*h (r*|fourierCoeff (signField f) {i}|) := by
  have he := S6 i f hr₀ hr₁
  have hm := MeanCorrection.mean_correction hr₀ hr₁
    (abs_nonneg (fourierCoeff (signField f) {i}))
    (mean_abs_add_singleton_abs_le_one i (signField_mem_Icc f))
  rw [information_eq_phiEntropy]
  unfold phiEntropy phi
  rw [cubeExpect_sub, cubeExpect_const, cubeExpect_noise]
  unfold phi at hm
  nlinarith

/-- Exact sufficient CK criterion (S8) from scalar.tex. -/
theorem ck_of_S8 {n : ℕ} (i : Fin n) (f : Cube n → Bool) {r : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1)
    (hcrit : 0 ≤ (1-r^2)*h (r*|fourierCoeff (signField f) {i}|) -
      (1-r^2*|fourierCoeff (signField f) {i}|)*h r) :
    information f r ≤ phi r := by
  have hi := information_influential_upper i f hr₀ hr₁
  unfold phi
  nlinarith

end MostInformativeBit
