import MostInformativeBit.InfluentialCoordinate
import MostInformativeBit.CubeLogSobolev

/-! Pivotal sections of a Boolean function (mechanism.tex, Section "Edge
Geometry and the Pivotal Decomposition"). Sections are kept on the same cube:
`sectionDiff i v x = (v (x with i := +1) - v (x with i := -1)) / 2`, which does
not depend on `x i`. Fourier coefficients, the pivotal mean `a_i = f̂({i})`, the
Parseval identity `∑_{S ∋ i} f̂(S)^2 = a_i`, and the coordinate re-indexing
identities are proved for actual functions. -/
namespace MostInformativeBit
open scoped BigOperators

/-! ### Re-indexing sums over coordinates and Fourier sets -/

theorem sum_insert_reindex {n : ℕ} (i : Fin n) (G : Finset (Fin n) → ℝ) :
    (∑ S : Finset (Fin n), if i ∈ S then 0 else G (insert i S)) =
      ∑ T : Finset (Fin n), if i ∈ T then G T else 0 := by
  rw [show (∑ S : Finset (Fin n), if i ∈ S then 0 else G (insert i S)) =
      ∑ S ∈ Finset.univ.filter (fun S => i ∉ S), G (insert i S) by
        rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro S _; split_ifs <;> simp_all,
    show (∑ T : Finset (Fin n), if i ∈ T then G T else 0) =
      ∑ T ∈ Finset.univ.filter (fun T => i ∈ T), G T by rw [Finset.sum_filter]]
  apply Finset.sum_nbij' (insert i) (fun T => T.erase i)
  · intro S hS; simp at hS ⊢
  · intro T hT; simp at hT ⊢
  · intro S hS
    have hS' : i ∉ S := by simpa using hS
    exact Finset.erase_insert hS'
  · intro T hT
    have hT' : i ∈ T := by simpa using hT
    exact Finset.insert_erase hT'
  · intro S _; rfl

theorem sum_coord_mem {n : ℕ} (G : Finset (Fin n) → ℝ) :
    (∑ i : Fin n, ∑ T : Finset (Fin n), if i ∈ T then G T else 0) =
      ∑ T : Finset (Fin n), (T.card : ℝ) * G T := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

theorem sum_coord_insert {n : ℕ} (G : Finset (Fin n) → ℝ) :
    (∑ i : Fin n, ∑ S : Finset (Fin n), if i ∈ S then 0 else G (insert i S)) =
      ∑ T : Finset (Fin n), (T.card : ℝ) * G T := by
  simp_rw [sum_insert_reindex]
  exact sum_coord_mem G

/-! ### Section derivative and its Fourier coefficients -/

/-- The source's `(v_{i,+} - v_{i,-}) / 2`, kept on the full cube. -/
noncomputable def sectionDiff {n : ℕ} (i : Fin n) (v : Cube n → ℝ) (x : Cube n) : ℝ :=
  (v (Function.update x i true) - v (Function.update x i false)) / 2

theorem sectionDiff_flip {n : ℕ} (i : Fin n) (v : Cube n → ℝ) (x : Cube n) :
    sectionDiff i v (cubeFlip i x) = sectionDiff i v x := by
  simp [sectionDiff, cubeFlip, Function.update_idem]

theorem character_update {n : ℕ} (T : Finset (Fin n)) (i : Fin n) (b : Bool) (x : Cube n) :
    character T (Function.update x i b) =
      if i ∈ T then cubeSign b * character (T.erase i) x else character T x := by
  unfold character
  split_ifs with hi
  · rw [← Finset.mul_prod_erase T _ hi, Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  · apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (by rintro rfl; exact hi hj)]

theorem sectionDiff_expansion {n : ℕ} (i : Fin n) (v : Cube n → ℝ) (x : Cube n) :
    sectionDiff i v x = ∑ T : Finset (Fin n),
      fourierCoeff v T * (if i ∈ T then character (T.erase i) x else 0) := by
  unfold sectionDiff
  rw [← fourier_expansion v (Function.update x i true),
    ← fourier_expansion v (Function.update x i false), ← Finset.sum_sub_distrib,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro T _
  simp only [character_update]
  split_ifs <;> simp [cubeSign]

theorem fourierCoeff_sectionDiff {n : ℕ} (i : Fin n) (v : Cube n → ℝ) (S : Finset (Fin n)) :
    fourierCoeff (sectionDiff i v) S =
      if i ∈ S then 0 else fourierCoeff v (insert i S) := by
  classical
  have h1 : fourierCoeff (sectionDiff i v) S = ∑ T : Finset (Fin n),
      fourierCoeff v T * (if i ∈ T then (if T.erase i = S then 1 else 0) else 0) := by
    change cubeExpect (fun x => sectionDiff i v x * character S x) = _
    simp_rw [sectionDiff_expansion, Finset.sum_mul]
    rw [cubeExpect_sum]
    apply Finset.sum_congr rfl
    intro T _
    by_cases hT : i ∈ T
    · simp only [hT, if_true]
      rw [show (fun x => fourierCoeff v T * character (T.erase i) x * character S x) =
          fun x => fourierCoeff v T * (character (T.erase i) x * character S x) by
            ext x; ring, cubeExpect_mul, character_orthogonality]
    · simp [hT]
  rw [h1]
  split_ifs with hS
  · apply Finset.sum_eq_zero
    intro T _
    split_ifs with hT hE
    · exact absurd (hE ▸ hS) (Finset.notMem_erase i T)
    · simp
    · simp
  · rw [Finset.sum_eq_single (insert i S)]
    · simp [Finset.erase_insert hS]
    · intro T _ hne
      split_ifs with hT hE
      · exact absurd (by rw [← hE, Finset.insert_erase hT]) hne
      · simp
      · simp
    · simp

theorem cubeExpect_sectionDiff {n : ℕ} (i : Fin n) (v : Cube n → ℝ) :
    cubeExpect (sectionDiff i v) = fourierCoeff v {i} := by
  rw [← fourierCoeff_empty, fourierCoeff_sectionDiff]
  simp

/-- Section differences commute with the BSC, up to the factor `r`. -/
theorem sectionDiff_noise {n : ℕ} (i : Fin n) (r : ℝ) (v : Cube n → ℝ) :
    sectionDiff i (noise r v) = fun x => r * noise r (sectionDiff i v) x := by
  funext x
  rw [← fourier_expansion (sectionDiff i (noise r v)) x, noise_expansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  simp only [fourierCoeff_sectionDiff, fourierCoeff_noise]
  split_ifs with hS
  · simp
  · rw [Finset.card_insert_of_notMem hS]; ring

/-! ### Pivotal indicators of monotone Boolean functions -/

/-- The source's pivotal indicator `q_i^f = (f_{i,+} - f_{i,-})/2`. -/
noncomputable def pivotal {n : ℕ} (i : Fin n) (f : Cube n → Bool) : Cube n → ℝ :=
  sectionDiff i (signField f)

/-- The pivotal mean `a_i`. -/
noncomputable def pivotalMean {n : ℕ} (i : Fin n) (f : Cube n → Bool) : ℝ :=
  fourierCoeff (signField f) {i}

theorem cubeExpect_pivotal {n : ℕ} (i : Fin n) (f : Cube n → Bool) :
    cubeExpect (pivotal i f) = pivotalMean i f :=
  cubeExpect_sectionDiff i _

theorem fourierCoeff_pivotal {n : ℕ} (i : Fin n) (f : Cube n → Bool) (S : Finset (Fin n)) :
    fourierCoeff (pivotal i f) S =
      if i ∈ S then 0 else fourierCoeff (signField f) (insert i S) :=
  fourierCoeff_sectionDiff i _ S

theorem update_false_le_true {n : ℕ} (i : Fin n) (x : Cube n) :
    Function.update x i false ≤ Function.update x i true := by
  intro j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

theorem pivotal_eq_zero_or_one {n : ℕ} {f : Cube n → Bool} (hf : Monotone f)
    (i : Fin n) (x : Cube n) : pivotal i f x = 0 ∨ pivotal i f x = 1 := by
  have hle := hf (update_false_le_true i x)
  unfold pivotal sectionDiff signField
  cases h0 : f (Function.update x i false) <;> cases h1 : f (Function.update x i true) <;>
    simp_all [cubeSign, Bool.le_iff_imp]

theorem pivotal_nonneg {n : ℕ} {f : Cube n → Bool} (hf : Monotone f) (i : Fin n)
    (x : Cube n) : 0 ≤ pivotal i f x := by
  rcases pivotal_eq_zero_or_one hf i x with h | h <;> rw [h] <;> norm_num

theorem pivotal_sq {n : ℕ} {f : Cube n → Bool} (hf : Monotone f) (i : Fin n)
    (x : Cube n) : pivotal i f x ^ 2 = pivotal i f x := by
  rcases pivotal_eq_zero_or_one hf i x with h | h <;> rw [h] <;> norm_num

/-- For monotone `f`, the source's indicator agrees with the pivotal-edge indicator. -/
theorem pivotal_eq_pivotalIndicator {n : ℕ} {f : Cube n → Bool} (hf : Monotone f)
    (i : Fin n) : pivotal i f = pivotalIndicator i f := by
  funext x
  have hle := hf (update_false_le_true i x)
  unfold pivotal sectionDiff signField pivotalIndicator
  cases h0 : f (Function.update x i false) <;> cases h1 : f (Function.update x i true) <;>
    simp_all [cubeSign, Bool.le_iff_imp]

theorem pivotalMean_eq_influence {n : ℕ} {f : Cube n → Bool} (hf : Monotone f) (i : Fin n) :
    pivotalMean i f = pivotalProbability i f := by
  rw [← cubeExpect_pivotal, pivotal_eq_pivotalIndicator hf]; rfl

theorem pivotalMean_nonneg {n : ℕ} {f : Cube n → Bool} (hf : Monotone f) (i : Fin n) :
    0 ≤ pivotalMean i f := by
  rw [← cubeExpect_pivotal]; exact cubeExpect_nonneg (pivotal_nonneg hf i)

/-- Parseval for the pivotal indicator: total squared Fourier mass `a_i`. -/
theorem sum_sq_fourierCoeff_pivotal {n : ℕ} {f : Cube n → Bool} (hf : Monotone f)
    (i : Fin n) :
    (∑ S : Finset (Fin n), fourierCoeff (pivotal i f) S ^ 2) = pivotalMean i f := by
  rw [← parseval, ← cubeExpect_pivotal]
  congr 1; funext x; exact pivotal_sq hf i x

/-- The source's identity `∑_{S ∋ i} f̂(S)^2 = a_i`. -/
theorem sum_sq_fourierCoeff_mem {n : ℕ} {f : Cube n → Bool} (hf : Monotone f) (i : Fin n) :
    (∑ T : Finset (Fin n), if i ∈ T then fourierCoeff (signField f) T ^ 2 else 0) =
      pivotalMean i f := by
  rw [← sum_sq_fourierCoeff_pivotal hf i, ← sum_insert_reindex]
  apply Finset.sum_congr rfl
  intro S _
  rw [fourierCoeff_pivotal]
  split_ifs <;> simp

theorem pivotalMean_le_one {n : ℕ} {f : Cube n → Bool} (hf : Monotone f) (i : Fin n) :
    pivotalMean i f ≤ 1 := by
  rw [← cubeExpect_pivotal]
  simpa using cubeExpect_mono (fun x => by
    rcases pivotal_eq_zero_or_one hf i x with h | h <;> rw [h] <;> norm_num :
      ∀ x, pivotal i f x ≤ 1)

/-- A zero pivotal mean forces the pivotal indicator to vanish. -/
theorem pivotal_eq_zero_of_mean {n : ℕ} {f : Cube n → Bool} (hf : Monotone f) (i : Fin n)
    (h : pivotalMean i f = 0) (x : Cube n) : pivotal i f x = 0 := by
  have hsum : ∑ y, pivotal i f y = 0 := by
    have hwt : GeneralCK.Information.cubeWeight n ≠ 0 := by
      unfold GeneralCK.Information.cubeWeight; positivity
    have : GeneralCK.Information.cubeWeight n * ∑ y, pivotal i f y = 0 := by
      rw [← h, ← cubeExpect_pivotal]; rfl
    exact (mul_eq_zero.mp this).resolve_left hwt
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => pivotal_nonneg hf i y)).mp hsum x
    (Finset.mem_univ x)

theorem fourierCoeff_pivotal_eq_zero_of_mean {n : ℕ} {f : Cube n → Bool} (hf : Monotone f)
    (i : Fin n) (h : pivotalMean i f = 0) (S : Finset (Fin n)) :
    fourierCoeff (pivotal i f) S = 0 := by
  have : pivotal i f = fun _ => 0 := funext (pivotal_eq_zero_of_mean hf i h)
  rw [this]
  simp [fourierCoeff, cubeExpect]

/-- The source's `p_i = (u_{i,+} - u_{i,-})/2 = r T_r q_i` for `u = T_r f`. -/
theorem sectionDiff_noise_signField {n : ℕ} (i : Fin n) (r : ℝ) (f : Cube n → Bool) :
    sectionDiff i (noise r (signField f)) = fun x => r * noise r (pivotal i f) x :=
  sectionDiff_noise i r _

end MostInformativeBit
