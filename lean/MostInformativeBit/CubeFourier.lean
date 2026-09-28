import MostInformativeBit.Definitions

/-! Finite real Walsh analysis, with the paper's uniform normalization and
correlation parameter. The noise operator is the existing BSC kernel. -/
namespace MostInformativeBit
open scoped BigOperators

noncomputable def cubeExpect {n : ℕ} (v : Cube n → ℝ) : ℝ :=
  GeneralCK.Information.cubeWeight n * ∑ x, v x

/-- `false` represents -1 and `true` represents +1. -/
def cubeSign (b : Bool) : ℝ := if b then 1 else -1

noncomputable def character {n : ℕ} (S : Finset (Fin n)) (x : Cube n) : ℝ :=
  ∏ i ∈ S, cubeSign (x i)

noncomputable def fourierCoeff {n : ℕ} (v : Cube n → ℝ) (S : Finset (Fin n)) : ℝ :=
  cubeExpect (fun x => v x * character S x)

noncomputable def noise {n : ℕ} (r : ℝ) (v : Cube n → ℝ) (y : Cube n) : ℝ :=
  ∑ x, GeneralCK.noiseKernel ((1-r)/2) x y * v x

@[simp] theorem cubeSign_sq (b : Bool) : cubeSign b ^ 2 = 1 := by
  cases b <;> norm_num [cubeSign]

@[simp] theorem cubeExpect_const {n : ℕ} (c : ℝ) :
    cubeExpect (fun _ : Cube n => c) = c := by
  have hw := GeneralCK.Information.weight_sum n
  simpa [cubeExpect, ← Finset.sum_mul, ← Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using congrArg (· * c) hw

theorem cubeExpect_add {n : ℕ} (v w : Cube n → ℝ) :
    cubeExpect (fun x => v x + w x) = cubeExpect v + cubeExpect w := by
  simp [cubeExpect, Finset.sum_add_distrib, mul_add]

theorem cubeExpect_sub {n : ℕ} (v w : Cube n → ℝ) :
    cubeExpect (fun x => v x - w x) = cubeExpect v - cubeExpect w := by
  simp [cubeExpect, Finset.sum_sub_distrib, mul_sub]

theorem cubeExpect_mul {n : ℕ} (c : ℝ) (v : Cube n → ℝ) :
    cubeExpect (fun x => c * v x) = c * cubeExpect v := by
  simp [cubeExpect, ← Finset.mul_sum, mul_left_comm]

theorem cubeExpect_sum {n : ℕ} {ι : Type*} (s : Finset ι) (v : ι → Cube n → ℝ) :
    cubeExpect (fun x => ∑ i ∈ s, v i x) = ∑ i ∈ s, cubeExpect (v i) := by
  simp only [cubeExpect, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem cubeExpect_nonneg {n : ℕ} {v : Cube n → ℝ} (hv : ∀ x, 0 ≤ v x) :
    0 ≤ cubeExpect v := by
  apply mul_nonneg (by unfold GeneralCK.Information.cubeWeight; positivity)
  exact Finset.sum_nonneg (fun x _ => hv x)

theorem cubeExpect_mono {n : ℕ} {v w : Cube n → ℝ} (h : ∀ x, v x ≤ w x) :
    cubeExpect v ≤ cubeExpect w := by
  apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => h x))
  unfold GeneralCK.Information.cubeWeight
  positivity

/-- Finite product measure factorization; valid for arbitrary real factors. -/
theorem cubeExpect_prod {n : ℕ} (q : Fin n → Bool → ℝ) :
    cubeExpect (fun x => ∏ i, q i (x i)) = ∏ i, (q i false + q i true) / 2 := by
  have hs := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset Bool)) q
  rw [Fintype.piFinset_univ] at hs
  rw [cubeExpect, ← hs]
  simp only [Fintype.sum_bool, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, GeneralCK.Information.cubeWeight,
    zpow_neg, zpow_natCast]
  rw [mul_comm, div_eq_mul_inv]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  ring

 theorem character_eq_prod {n : ℕ} (S : Finset (Fin n)) (x : Cube n) :
    character S x = ∏ i, if i ∈ S then cubeSign (x i) else 1 := by
  classical
  simp [character]

@[simp] theorem character_empty {n : ℕ} (x : Cube n) : character ∅ x = 1 := by
  simp [character]

@[simp] theorem character_sq {n : ℕ} (S : Finset (Fin n)) (x : Cube n) :
    character S x ^ 2 = 1 := by
  simp [character, ← Finset.prod_pow]

/-- Orthonormality of the real Walsh characters. -/
theorem character_orthogonality {n : ℕ} (S T : Finset (Fin n)) :
    cubeExpect (fun x => character S x * character T x) = if S = T then 1 else 0 := by
  classical
  simp_rw [character_eq_prod, ← Finset.prod_mul_distrib]
  rw [cubeExpect_prod (fun i b => (if i ∈ S then cubeSign b else 1) *
    (if i ∈ T then cubeSign b else 1))]
  have hc (i : Fin n) :
      ((if i ∈ S then cubeSign false else 1) * (if i ∈ T then cubeSign false else 1) +
       (if i ∈ S then cubeSign true else 1) * (if i ∈ T then cubeSign true else 1)) / 2 =
       if (i ∈ S ↔ i ∈ T) then 1 else 0 := by
    by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;> norm_num [hs, ht, cubeSign]
  simp_rw [hc]
  by_cases h : S = T
  · simp [h]
  · rw [if_neg h]
    have hex : ∃ i, ¬(i ∈ S ↔ i ∈ T) := by
      by_contra hn
      push Not at hn
      exact h (Finset.ext hn)
    obtain ⟨i, hi⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

@[simp] theorem noise_const {n : ℕ} (r c : ℝ) :
    noise r (fun _ : Cube n => c) = fun _ => c := by
  funext y
  simp [noise, ← Finset.sum_mul, GeneralCK.Information.kernel_column_sum]

theorem noise_add {n : ℕ} (r : ℝ) (v w : Cube n → ℝ) :
    noise r (fun x => v x + w x) = fun x => noise r v x + noise r w x := by
  funext y
  simp [noise, mul_add, Finset.sum_add_distrib]

theorem noise_mul {n : ℕ} (r c : ℝ) (v : Cube n → ℝ) :
    noise r (fun x => c * v x) = fun x => c * noise r v x := by
  funext y
  simp [noise, Finset.mul_sum, mul_left_comm]

theorem noise_sum {n : ℕ} {ι : Type*} (s : Finset ι) (r : ℝ) (v : ι → Cube n → ℝ) :
    noise r (fun x => ∑ i ∈ s, v i x) = fun x => ∑ i ∈ s, noise r (v i) x := by
  funext y
  simp only [noise, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem cubeExpect_noise {n : ℕ} (r : ℝ) (v : Cube n → ℝ) :
    cubeExpect (noise r v) = cubeExpect v := by
  unfold cubeExpect noise
  rw [Finset.sum_comm]
  simp [← Finset.sum_mul, GeneralCK.noiseKernel_sum]

/-- Spectral diagonalization of the actual finite BSC operator. -/
theorem noise_character {n : ℕ} (r : ℝ) (S : Finset (Fin n)) (y : Cube n) :
    noise r (character S) y = r ^ S.card * character S y := by
  classical
  simp only [noise, GeneralCK.noiseKernel, character_eq_prod, ← Finset.prod_mul_distrib]
  have hs := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset Bool))
    (fun i b => (if b = y i then 1 - (1-r)/2 else (1-r)/2) *
      (if i ∈ S then cubeSign b else 1))
  rw [Fintype.piFinset_univ] at hs
  rw [← hs]
  have hc (i : Fin n) :
      (∑ b : Bool, (if b = y i then 1 - (1-r)/2 else (1-r)/2) *
        (if i ∈ S then cubeSign b else 1)) =
      if i ∈ S then r * cubeSign (y i) else 1 := by
    by_cases hi : i ∈ S <;> cases hy : y i <;> simp [hi, cubeSign] <;> ring
  simp_rw [hc]
  simp only [Finset.prod_ite_mem_eq, Finset.prod_mul_distrib, Finset.prod_const]

/-- Completeness kernel of the Walsh system. -/
theorem character_complete {n : ℕ} (x y : Cube n) :
    (∑ S : Finset (Fin n), character S x * character S y) =
      if x = y then (2 : ℝ)^n else 0 := by
  classical
  simp only [character, ← Finset.prod_mul_distrib]
  have hp := Fintype.prod_add (fun i : Fin n => cubeSign (x i) * cubeSign (y i))
    (fun _ => (1 : ℝ))
  simp only [Finset.prod_const_one, mul_one] at hp
  rw [← hp]
  by_cases h : x = y
  · subst y
    simp only [← pow_two, cubeSign_sq]
    norm_num
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hh
      push Not at hh
      exact h (funext hh)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    cases hx : x i <;> cases hy : y i <;> simp_all [cubeSign]

/-- Fourier inversion for every real cube field. -/
theorem fourier_expansion {n : ℕ} (v : Cube n → ℝ) (x : Cube n) :
    (∑ S : Finset (Fin n), fourierCoeff v S * character S x) = v x := by
  classical
  calc
    (∑ S, fourierCoeff v S * character S x) =
        GeneralCK.Information.cubeWeight n *
          ∑ y, v y * (∑ S : Finset (Fin n), character S y * character S x) := by
      simp only [fourierCoeff, cubeExpect, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro S _
      ring
    _ = v x := by
      simp only [character_complete]
      simp [GeneralCK.Information.cubeWeight, zpow_neg, zpow_natCast,
        mul_ite, mul_comm]

/-- Plancherel's bilinear identity, from finite Fourier inversion. -/
theorem fourier_inner {n : ℕ} (v w : Cube n → ℝ) :
    cubeExpect (fun x => v x * w x) =
      ∑ S : Finset (Fin n), fourierCoeff v S * fourierCoeff w S := by
  calc
    cubeExpect (fun x => v x * w x) =
        cubeExpect (fun x => ∑ S : Finset (Fin n),
          fourierCoeff w S * (v x * character S x)) := by
      congr 1
      funext x
      rw [← fourier_expansion w x]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ring
    _ = _ := by
      rw [cubeExpect_sum]
      simp_rw [cubeExpect_mul]
      simp only [fourierCoeff, mul_comm]

/-- Parseval, including dimension zero and arbitrary real fields. -/
theorem parseval {n : ℕ} (v : Cube n → ℝ) :
    cubeExpect (fun x => v x ^ 2) =
      ∑ S : Finset (Fin n), fourierCoeff v S ^ 2 := by
  simpa only [pow_two] using fourier_inner v v

@[simp] theorem fourierCoeff_character {n : ℕ} (S T : Finset (Fin n)) :
    fourierCoeff (character S) T = if S = T then 1 else 0 :=
  character_orthogonality S T

@[simp] theorem fourierCoeff_empty {n : ℕ} (v : Cube n → ℝ) :
    fourierCoeff v ∅ = cubeExpect v := by
  simp [fourierCoeff]

/-- The kernel operator agrees with the paper's spectral noise formula. -/
theorem noise_expansion {n : ℕ} (r : ℝ) (v : Cube n → ℝ) (x : Cube n) :
    noise r v x = ∑ S : Finset (Fin n),
      r ^ S.card * fourierCoeff v S * character S x := by
  have hv : v = fun y => ∑ S : Finset (Fin n), fourierCoeff v S * character S y :=
    funext (fun y => (fourier_expansion v y).symm)
  conv_lhs => rw [hv]
  rw [noise_sum]
  simp only [noise_mul, noise_character]
  apply Finset.sum_congr rfl
  intro S _
  ring

/-- Fourier coefficients diagonalize the BSC for every real correlation. -/
theorem fourierCoeff_noise {n : ℕ} (r : ℝ) (v : Cube n → ℝ) (S : Finset (Fin n)) :
    fourierCoeff (noise r v) S = r ^ S.card * fourierCoeff v S := by
  classical
  unfold fourierCoeff
  simp_rw [noise_expansion, Finset.sum_mul, mul_assoc]
  rw [cubeExpect_sum]
  simp only [cubeExpect_mul, character_orthogonality, mul_ite, mul_one, mul_zero]
  simp [fourierCoeff]

/-- The semigroup law is obtained from the actual kernel, not postulated. -/
theorem noise_comp {n : ℕ} (r s : ℝ) (v : Cube n → ℝ) :
    noise r (noise s v) = noise (r*s) v := by
  funext x
  rw [noise_expansion, noise_expansion]
  simp only [fourierCoeff_noise, mul_pow]
  apply Finset.sum_congr rfl
  intro S _
  ring

@[simp] theorem noise_one {n : ℕ} (v : Cube n → ℝ) : noise 1 v = v := by
  funext x
  simpa [noise_expansion] using fourier_expansion v x

@[simp] theorem noise_zero {n : ℕ} (v : Cube n → ℝ) :
    noise 0 v = fun _ => cubeExpect v := by
  funext y
  simp only [noise, sub_zero, GeneralCK.Information.kernel_half, cubeExpect, Finset.mul_sum]

/-- Basic smoothed energy identity used throughout the manuscript. -/
theorem noise_energy {n : ℕ} (r : ℝ) (v : Cube n → ℝ) :
    cubeExpect (fun x => noise r v x ^ 2) =
      ∑ S : Finset (Fin n), r ^ (2*S.card) * fourierCoeff v S ^ 2 := by
  rw [parseval]
  simp_rw [fourierCoeff_noise, mul_pow, ← pow_mul, Nat.mul_comm _ 2]

/-- Coordinate flip; `false` and `true` encode -1 and +1. -/
def cubeFlip {n : ℕ} (i : Fin n) (x : Cube n) : Cube n :=
  Function.update x i (!(x i))

@[simp] theorem cubeFlip_self {n : ℕ} (i : Fin n) (x : Cube n) :
    cubeFlip i x i = !(x i) := by simp [cubeFlip]

@[simp] theorem cubeFlip_other {n : ℕ} (i j : Fin n) (x : Cube n) (hji : j ≠ i) :
    cubeFlip i x j = x j := by simp [cubeFlip, hji]

@[simp] theorem cubeFlip_involutive {n : ℕ} (i : Fin n) (x : Cube n) :
    cubeFlip i (cubeFlip i x) = x := by
  funext j
  by_cases hj : j = i
  · subst j; simp
  · simp [hj]

@[simp] theorem cubeSign_not (b : Bool) : cubeSign (!b) = -cubeSign b := by
  cases b <;> norm_num [cubeSign]

theorem character_flip {n : ℕ} (S : Finset (Fin n)) (i : Fin n) (x : Cube n) :
    character S (cubeFlip i x) = if i ∈ S then -character S x else character S x := by
  have hc (j : Fin n) : cubeSign (cubeFlip i x j) =
      (if j = i then -1 else 1) * cubeSign (x j) := by
    by_cases hj : j = i
    · subst j; simp
    · simp [hj]
  simp only [character, hc, Finset.prod_mul_distrib]
  classical
  simp only [Finset.prod_ite_eq', ite_mul, neg_one_mul, one_mul]

/-- The edge derivative has the normalization used in mechanism.tex. -/
noncomputable def cubeDerivative {n : ℕ} (i : Fin n) (v : Cube n → ℝ) (x : Cube n) : ℝ :=
  (v x - v (cubeFlip i x)) / 2

noncomputable def cubeLaplacian {n : ℕ} (v : Cube n → ℝ) (x : Cube n) : ℝ :=
  ∑ i, cubeDerivative i v x

theorem cubeDerivative_character {n : ℕ} (S : Finset (Fin n)) (i : Fin n) (x : Cube n) :
    cubeDerivative i (character S) x = if i ∈ S then character S x else 0 := by
  rw [cubeDerivative, character_flip]
  split_ifs <;> ring

theorem cubeLaplacian_character {n : ℕ} (S : Finset (Fin n)) (x : Cube n) :
    cubeLaplacian (character S) x = (S.card : ℝ) * character S x := by
  classical
  simp [cubeLaplacian, cubeDerivative_character]

theorem cubeLaplacian_mul {n : ℕ} (c : ℝ) (v : Cube n → ℝ) :
    cubeLaplacian (fun x => c * v x) = fun x => c * cubeLaplacian v x := by
  funext x
  simp only [cubeLaplacian, cubeDerivative, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem cubeLaplacian_sum {n : ℕ} {ι : Type*} (s : Finset ι) (v : ι → Cube n → ℝ) :
    cubeLaplacian (fun x => ∑ i ∈ s, v i x) = fun x => ∑ i ∈ s, cubeLaplacian (v i) x := by
  funext x
  simp only [cubeLaplacian, cubeDerivative, ← Finset.sum_sub_distrib, Finset.sum_div]
  rw [Finset.sum_comm]

/-- The edge Laplacian equals the degree multiplier, with no analytic assumptions. -/
theorem cubeLaplacian_expansion {n : ℕ} (v : Cube n → ℝ) (x : Cube n) :
    cubeLaplacian v x = ∑ S : Finset (Fin n),
      (S.card : ℝ) * fourierCoeff v S * character S x := by
  have hv : v = fun y => ∑ S : Finset (Fin n), fourierCoeff v S * character S y :=
    funext (fun y => (fourier_expansion v y).symm)
  conv_lhs => rw [hv]
  rw [cubeLaplacian_sum]
  simp only [cubeLaplacian_mul, cubeLaplacian_character]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem fourierCoeff_cubeLaplacian {n : ℕ} (v : Cube n → ℝ) (S : Finset (Fin n)) :
    fourierCoeff (cubeLaplacian v) S = (S.card : ℝ) * fourierCoeff v S := by
  classical
  unfold fourierCoeff
  simp_rw [cubeLaplacian_expansion, Finset.sum_mul, mul_assoc]
  rw [cubeExpect_sum]
  simp only [cubeExpect_mul, character_orthogonality, mul_ite, mul_one, mul_zero]
  simp [fourierCoeff]

/-- Degree-weighted energy in the normalization L chi_S = |S| chi_S. -/
theorem laplacian_energy {n : ℕ} (v : Cube n → ℝ) :
    cubeExpect (fun x => v x * cubeLaplacian v x) =
      ∑ S : Finset (Fin n), (S.card : ℝ) * fourierCoeff v S ^ 2 := by
  rw [fourier_inner]
  simp_rw [fourierCoeff_cubeLaplacian]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem noise_laplacian_energy {n : ℕ} (r : ℝ) (v : Cube n → ℝ) :
    cubeExpect (fun x => noise r v x * cubeLaplacian (noise r v) x) =
      ∑ S : Finset (Fin n), (S.card : ℝ) * r ^ (2*S.card) * fourierCoeff v S ^ 2 := by
  rw [laplacian_energy]
  simp_rw [fourierCoeff_noise, mul_pow, ← pow_mul, Nat.mul_comm _ 2, mul_assoc]

/-- Differentiating the finite spectral polynomial requires no limiting argument. -/
theorem noise_hasDerivAt {n : ℕ} (v : Cube n → ℝ) (x : Cube n) (r : ℝ) :
    HasDerivAt (fun t => noise t v x)
      (∑ S : Finset (Fin n), (S.card : ℝ) * r ^ (S.card-1) *
        fourierCoeff v S * character S x) r := by
  have hs := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Finset (Fin n))))
    (fun S _ => ((hasDerivAt_pow S.card r).mul_const (fourierCoeff v S)).mul_const (character S x))
  simpa only [noise_expansion] using hs

/-- The paper's generator identity, also valid at correlation zero. -/
theorem noise_deriv_laplacian {n : ℕ} (v : Cube n → ℝ) (x : Cube n) (r : ℝ) :
    r * deriv (fun t => noise t v x) r = cubeLaplacian (noise r v) x := by
  rw [(noise_hasDerivAt v x r).deriv, cubeLaplacian_expansion]
  simp only [fourierCoeff_noise, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : S.card = 0
  · simp [hS]
  · have hp : r * r ^ (S.card-1) = r ^ S.card := by
      rw [← pow_succ']
      congr 1
      omega
    calc
      r * ((S.card : ℝ) * r ^ (S.card-1) * fourierCoeff v S * character S x) =
          (S.card : ℝ) * (r*r^(S.card-1)) * fourierCoeff v S * character S x := by ring
      _ = _ := by rw [hp]; ring

theorem noise_hasDerivAt_laplacian {n : ℕ} (v : Cube n → ℝ) (x : Cube n) {r : ℝ}
    (hr : r ≠ 0) : HasDerivAt (fun t => noise t v x) (cubeLaplacian (noise r v) x / r) r := by
  have hd := noise_deriv_laplacian v x r
  have he : deriv (fun t => noise t v x) r = cubeLaplacian (noise r v) x / r := by
    apply (eq_div_iff hr).mpr
    simpa only [mul_comm] using hd
  rw [← he]
  exact (noise_hasDerivAt v x r).differentiableAt.hasDerivAt

end MostInformativeBit
