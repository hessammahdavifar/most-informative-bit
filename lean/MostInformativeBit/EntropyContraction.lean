import MostInformativeBit.CubeFourier

/-! Natural-log entropy identities and an explicitly conditional reduction of
(S6a) to ordinary entropy contraction. The substantive Gross contraction is
not assumed as an axiom and is not asserted as a theorem in this module. -/
namespace MostInformativeBit
open scoped BigOperators

/-- Natural entropy, including the continuous value at zero. -/
noncomputable def cubeEntropy {n : ℕ} (v : Cube n → ℝ) : ℝ :=
  -cubeExpect (fun x => Real.negMulLog (v x)) + Real.negMulLog (cubeExpect v)

noncomputable def phiEntropy {n : ℕ} (v : Cube n → ℝ) : ℝ :=
  cubeExpect (fun x => phi (v x)) - phi (cubeExpect v)

theorem cubeEntropy_eq_mul_log {n : ℕ} (v : Cube n → ℝ) :
    cubeEntropy v = cubeExpect (fun x => v x * Real.log (v x)) -
      cubeExpect v * Real.log (cubeExpect v) := by
  simp only [cubeEntropy, Real.negMulLog, neg_mul, cubeExpect, Finset.sum_neg_distrib,
    mul_neg, neg_neg]
  ring

@[simp] theorem cubeEntropy_const {n : ℕ} (c : ℝ) :
    cubeEntropy (fun _ : Cube n => c) = 0 := by simp [cubeEntropy]

@[simp] theorem phiEntropy_const {n : ℕ} (c : ℝ) :
    phiEntropy (fun _ : Cube n => c) = 0 := by simp [phiEntropy]

/-- The paper's logarithmic expression for phi, including the endpoints. -/
theorem two_phi_eq_negMulLog (t : ℝ) :
    2 * phi t = -Real.negMulLog (1+t) - Real.negMulLog (1-t) := by
  have he := GeneralCK.Information.scaled_binary_entropy 2 ((1-t)/2)
  rw [show 2*((1-t)/2) = 1-t by ring,
    show 2*(1-(1-t)/2) = 1+t by ring] at he
  have ht : Real.negMulLog 2 = -2 * Real.log 2 := rfl
  rw [ht] at he
  unfold phi h
  linarith

/-- Exact identity used by the source to pass from Gross entropy to phi entropy. -/
theorem two_phiEntropy_eq {n : ℕ} (v : Cube n → ℝ) :
    2 * phiEntropy v = cubeEntropy (fun x => 1+v x) + cubeEntropy (fun x => 1-v x) := by
  have havg : 2 * cubeExpect (fun x => phi (v x)) =
      -cubeExpect (fun x => Real.negMulLog (1+v x)) -
        cubeExpect (fun x => Real.negMulLog (1-v x)) := by
    rw [← cubeExpect_mul]
    simp_rw [two_phi_eq_negMulLog]
    rw [cubeExpect_sub]
    simp [cubeExpect, Finset.sum_neg_distrib]
  have hm := two_phi_eq_negMulLog (cubeExpect v)
  unfold phiEntropy cubeEntropy
  rw [cubeExpect_add, cubeExpect_sub, cubeExpect_const]
  linarith

theorem noise_mono {n : ℕ} {r : ℝ} (hr₀ : -1 ≤ r) (hr₁ : r ≤ 1)
    {v w : Cube n → ℝ} (hvw : ∀ x, v x ≤ w x) (y : Cube n) :
    noise r v y ≤ noise r w y := by
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left (hvw x)
  exact GeneralCK.noiseKernel_nonneg (by linarith) (by linarith) x y

theorem noise_mem_Icc {n : ℕ} {r a b : ℝ} (hr₀ : -1 ≤ r) (hr₁ : r ≤ 1)
    {v : Cube n → ℝ} (hv : ∀ x, v x ∈ Set.Icc a b) (y : Cube n) :
    noise r v y ∈ Set.Icc a b := by
  constructor
  · simpa only [noise_const] using noise_mono hr₀ hr₁ (fun x => (hv x).1) y
  · simpa only [noise_const] using noise_mono hr₀ hr₁ (fun x => (hv x).2) y

theorem cubeExpect_mem_Icc {n : ℕ} {a b : ℝ} {v : Cube n → ℝ}
    (hv : ∀ x, v x ∈ Set.Icc a b) : cubeExpect v ∈ Set.Icc a b := by
  constructor
  · simpa using cubeExpect_mono (fun x => (hv x).1)
  · simpa using cubeExpect_mono (fun x => (hv x).2)

theorem noise_one_add {n : ℕ} (r : ℝ) (v : Cube n → ℝ) :
    noise r (fun x => 1+v x) = fun x => 1+noise r v x := by
  rw [noise_add, noise_const]

theorem noise_one_sub {n : ℕ} (r : ℝ) (v : Cube n → ℝ) :
    noise r (fun x => 1-v x) = fun x => 1-noise r v x := by
  have hv : (fun x => 1-v x) = (fun x => 1+(-1)*v x) := by ext x; ring
  rw [hv, noise_add, noise_const, noise_mul]
  ext x
  ring

/-- Ordinary entropy contraction as a proposition; proved in `EntropyTensorization.lean`. -/
def CubeEntropyContraction (n : ℕ) (r : ℝ) : Prop :=
  ∀ v : Cube n → ℝ, (∀ x, 0 ≤ v x) → cubeEntropy (noise r v) ≤ r^2 * cubeEntropy v

/-- Exact S6a target, recorded as a proposition, not an assertion. -/
def PhiEntropyContraction (n : ℕ) (r : ℝ) : Prop :=
  ∀ v : Cube n → ℝ, (∀ x, v x ∈ Set.Icc (-1) 1) →
    phiEntropy (noise r v) ≤ r^2 * phiEntropy v

/-- Reduction only: the hypothesis is the substantive Gross entropy contraction. -/
theorem phiEntropyContraction_of_cubeEntropyContraction {n : ℕ} {r : ℝ}
    (hc : CubeEntropyContraction n r) : PhiEntropyContraction n r := by
  intro v hv
  have hp := hc (fun x => 1+v x) (fun x => by have := (hv x).1; linarith)
  have hm := hc (fun x => 1-v x) (fun x => by have := (hv x).2; linarith)
  rw [noise_one_add] at hp
  rw [noise_one_sub] at hm
  have hi := two_phiEntropy_eq v
  have ho := two_phiEntropy_eq (noise r v)
  nlinarith

@[simp] theorem phiEntropy_noise_zero {n : ℕ} (v : Cube n → ℝ) :
    phiEntropy (noise 0 v) = 0 := by simp

theorem phiEntropyContraction_zero (n : ℕ) : PhiEntropyContraction n 0 := by
  intro v _
  simp

theorem phiEntropyContraction_one (n : ℕ) : PhiEntropyContraction n 1 := by
  intro v _
  simp

/-- Convexity on the full closed interval, including the continuous endpoints. -/
theorem phi_convexOn : ConvexOn ℝ (Set.Icc (-1) 1) phi := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : (1-x)/2 ∈ Set.Icc (0:ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  have hy' : (1-y)/2 ∈ Set.Icc (0:ℝ) 1 := by constructor <;> linarith [hy.1, hy.2]
  have hc := Real.strictConcave_binEntropy.concaveOn.2 hx' hy' ha hb hab
  simp only [smul_eq_mul] at hc ⊢
  have he : (1-(a*x+b*y))/2 = a*((1-x)/2)+b*((1-y)/2) := by nlinarith [hab]
  unfold phi h
  rw [he]
  have hL : a * Real.log 2 + b * Real.log 2 = Real.log 2 := by
    rw [← add_mul, hab, one_mul]
  linarith

/-- Nonnegativity of phi entropy is Jensen's inequality. -/
theorem phiEntropy_nonneg {n : ℕ} {v : Cube n → ℝ}
    (hv : ∀ x, v x ∈ Set.Icc (-1) 1) : 0 ≤ phiEntropy v := by
  have hj := phi_convexOn.map_sum_le
    (t := Finset.univ) (w := fun _ : Cube n => GeneralCK.Information.cubeWeight n)
    (fun _ _ => by unfold GeneralCK.Information.cubeWeight; positivity)
    (GeneralCK.Information.weight_sum n) (fun x _ => hv x)
  simpa only [phiEntropy, cubeExpect, smul_eq_mul, ← Finset.mul_sum] using sub_nonneg.mpr hj

/-- Kernel Jensen inequality, with positivity restricted to valid BSC correlations. -/
theorem phi_noise_le {n : ℕ} {r : ℝ} (hr₀ : -1 ≤ r) (hr₁ : r ≤ 1)
    {v : Cube n → ℝ} (hv : ∀ x, v x ∈ Set.Icc (-1) 1) (y : Cube n) :
    phi (noise r v y) ≤ noise r (fun x => phi (v x)) y := by
  have hj := phi_convexOn.map_sum_le (t := Finset.univ)
    (w := fun x => GeneralCK.noiseKernel ((1-r)/2) x y)
    (fun x _ => GeneralCK.noiseKernel_nonneg (by linarith) (by linarith) x y)
    (GeneralCK.Information.kernel_column_sum ((1-r)/2) y) (fun x _ => hv x)
  simpa only [smul_eq_mul, noise] using hj

/-- Data processing. This factor-one bound is not the sharp S6a estimate. -/
theorem phiEntropy_noise_le {n : ℕ} {r : ℝ} (hr₀ : -1 ≤ r) (hr₁ : r ≤ 1)
    {v : Cube n → ℝ} (hv : ∀ x, v x ∈ Set.Icc (-1) 1) :
    phiEntropy (noise r v) ≤ phiEntropy v := by
  have he := cubeExpect_mono (phi_noise_le hr₀ hr₁ hv)
  rw [cubeExpect_noise] at he
  unfold phiEntropy
  rw [cubeExpect_noise]
  exact sub_le_sub_right he _

/-- Real sign representation of a Boolean decision rule. -/
def signField {n : ℕ} (f : Cube n → Bool) (x : Cube n) : ℝ := cubeSign (f x)

theorem signField_mem_Icc {n : ℕ} (f : Cube n → Bool) (x : Cube n) :
    signField f x ∈ Set.Icc (-1) 1 := by
  cases h : f x <;> norm_num [signField, cubeSign, h]

theorem signField_eq_indicator {n : ℕ} (f : Cube n → Bool) (x : Cube n) :
    signField f x = 2 * (if f x = true then (1:ℝ) else 0) - 1 := by
  cases h : f x <;> norm_num [signField, cubeSign, h]

theorem cubeExpect_signField {n : ℕ} (f : Cube n → Bool) :
    cubeExpect (signField f) = 2 * GeneralCK.Information.meanIndicator f - 1 := by
  change cubeExpect (fun x => signField f x) = _
  simp_rw [signField_eq_indicator]
  rw [cubeExpect_sub, cubeExpect_mul, cubeExpect_const]
  rfl

theorem noise_signField {n : ℕ} (r : ℝ) (f : Cube n → Bool) (y : Cube n) :
    noise r (signField f) y = 2 * GeneralCK.Information.posterior f ((1-r)/2) y - 1 := by
  classical
  unfold noise
  simp_rw [signField_eq_indicator, mul_sub]
  rw [Finset.sum_sub_distrib]
  simp only [mul_one, GeneralCK.Information.kernel_column_sum,
    GeneralCK.Information.posterior, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> ring

theorem h_two_mul_sub_one (t : ℝ) : h (2*t-1) = Real.binEntropy t := by
  unfold h
  rw [show (1-(2*t-1))/2 = 1-t by ring, Real.binEntropy_one_sub]

/-- The paper's posterior information identity in natural units. -/
theorem information_eq_phiEntropy {n : ℕ} (f : Cube n → Bool) (r : ℝ) :
    information f r = phiEntropy (noise r (signField f)) := by
  rw [information_eq_conditional_entropy]
  unfold phiEntropy phi
  rw [cubeExpect_sub, cubeExpect_const, cubeExpect_noise, cubeExpect_signField,
    h_two_mul_sub_one]
  simp_rw [noise_signField, h_two_mul_sub_one]
  unfold cubeExpect
  ring

/-- Boolean Parseval with the empty coefficient separated as the mean. -/
theorem signField_parseval {n : ℕ} (f : Cube n → Bool) :
    (∑ S : Finset (Fin n), fourierCoeff (signField f) S ^ 2) = 1 := by
  rw [← parseval]
  have hs : (fun x => signField f x ^ 2) = fun _ => (1 : ℝ) := by
    ext x
    exact cubeSign_sq (f x)
  rw [hs, cubeExpect_const]

end MostInformativeBit
