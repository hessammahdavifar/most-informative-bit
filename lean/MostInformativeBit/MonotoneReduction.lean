import MostInformativeBit.EntropyContraction

/-! Coordinate sorting, histogram-preserving monotone rearrangement, and
the manuscript's information-improvement inequality. All estimates are proved
directly for the existing finite BSC kernel. -/
namespace MostInformativeBit
open scoped BigOperators

/-- Sorting a coordinate places its lesser section value at `false`. -/
def coordinateSort {n : ℕ} {α : Type*} [LinearOrder α]
    (i : Fin n) (v : Cube n → α) (x : Cube n) : α :=
  if x i then max (v (Function.update x i false)) (v (Function.update x i true))
  else min (v (Function.update x i false)) (v (Function.update x i true))

def CoordinateMonotone {n : ℕ} {α : Type*} [Preorder α]
    (i : Fin n) (v : Cube n → α) : Prop :=
  ∀ x, v (Function.update x i false) ≤ v (Function.update x i true)

theorem coordinateSort_monotone {n : ℕ} {α : Type*} [LinearOrder α]
    (i : Fin n) (v : Cube n → α) : CoordinateMonotone i (coordinateSort i v) := by
  intro x
  simp only [coordinateSort, Function.update_self, Bool.false_eq_true, ↓reduceIte,
    Function.update_idem]
  exact min_le_max

/-- Sorting one coordinate preserves monotonicity already established in another. -/
theorem coordinateSort_preserves_monotone {n : ℕ} {α : Type*} [LinearOrder α]
    {i j : Fin n} (hij : i ≠ j) {v : Cube n → α} (hv : CoordinateMonotone j v) :
    CoordinateMonotone j (coordinateSort i v) := by
  intro x
  have h₀ := hv (Function.update x i false)
  have h₁ := hv (Function.update x i true)
  rw [Function.update_comm hij, Function.update_comm hij] at h₀ h₁
  simp only [coordinateSort, Function.update_of_ne hij]
  split_ifs
  · exact max_le_max h₀ h₁
  · exact min_le_min h₀ h₁

/-- Cube expectation is invariant under a coordinate flip. -/
theorem cubeExpect_flip {n : ℕ} (i : Fin n) (v : Cube n → ℝ) :
    cubeExpect (fun x => v (cubeFlip i x)) = cubeExpect v := by
  unfold cubeExpect
  congr 1
  exact Equiv.sum_comp (Function.Involutive.toPerm (cubeFlip i) (cubeFlip_involutive i)) v

/-- Sorting preserves the pair's multiset, even after an arbitrary observable. -/
theorem coordinateSort_pair {n : ℕ} {α : Type*} [LinearOrder α]
    (i : Fin n) (v : Cube n → α) (ψ : α → ℝ) (x : Cube n) :
    ψ (coordinateSort i v x) + ψ (coordinateSort i v (cubeFlip i x)) =
      ψ (v x) + ψ (v (cubeFlip i x)) := by
  have hp (a b : α) : ψ (min a b) + ψ (max a b) = ψ a + ψ b := by
    rcases le_total a b with hab | hba
    · rw [min_eq_left hab, max_eq_right hab]
    · rw [min_eq_right hba, max_eq_left hba, add_comm]
  cases hx : x i
  · have hx₀ : Function.update x i false = x := by
      simpa only [hx] using Function.update_eq_self i x
    simp only [coordinateSort, hx, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, cubeFlip, Function.update_idem, Function.update_self, hx₀]
    exact hp _ _
  · have hx₁ : Function.update x i true = x := by
      simpa only [hx] using Function.update_eq_self i x
    simp only [coordinateSort, hx, ↓reduceIte, Bool.not_true,
      Bool.false_eq_true, cubeFlip, Function.update_idem, Function.update_self, hx₁]
    simpa only [add_comm] using hp (v (Function.update x i false)) (v x)

/-- Every one-coordinate sort preserves the entire value distribution. -/
theorem cubeExpect_coordinateSort {n : ℕ} {α : Type*} [LinearOrder α]
    (i : Fin n) (v : Cube n → α) (ψ : α → ℝ) :
    cubeExpect (fun x => ψ (coordinateSort i v x)) = cubeExpect (fun x => ψ (v x)) := by
  have hpair : (fun x => ψ (coordinateSort i v x) + ψ (coordinateSort i v (cubeFlip i x))) =
      (fun x => ψ (v x) + ψ (v (cubeFlip i x))) := funext (coordinateSort_pair i v ψ)
  have he := congrArg (@cubeExpect n) hpair
  change cubeExpect (fun x => ψ (coordinateSort i v x) + ψ (coordinateSort i v (cubeFlip i x))) =
    cubeExpect (fun x => ψ (v x) + ψ (v (cubeFlip i x))) at he
  rw [cubeExpect_add, cubeExpect_add,
    cubeExpect_flip i (fun x => ψ (coordinateSort i v x)),
    cubeExpect_flip i (fun x => ψ (v x))] at he
  linarith

theorem coordinateMonotone_le_update {n : ℕ} {α : Type*} [Preorder α]
    {i : Fin n} {v : Cube n → α} (hv : CoordinateMonotone i v)
    (x : Cube n) (b : Bool) (hb : x i ≤ b) : v x ≤ v (Function.update x i b) := by
  have hpair (a b : Bool) (hab : a ≤ b) :
      v (Function.update x i a) ≤ v (Function.update x i b) := by
    cases a <;> cases b
    · exact le_rfl
    · exact hv x
    · exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) hab)
    · exact le_rfl
  simpa only [Function.update_eq_self] using hpair (x i) b hb

/-- Coordinatewise monotonicity implies the full product-order monotonicity. -/
theorem monotone_of_coordinateMonotone {n : ℕ} {α : Type*} [Preorder α]
    {v : Cube n → α} (hv : ∀ i, CoordinateMonotone i v) : Monotone v := by
  intro x y hxy
  classical
  let z (s : Finset (Fin n)) : Cube n := fun j => if j ∈ s then y j else x j
  have hs (s : Finset (Fin n)) : v x ≤ v (z s) := by
    induction s using Finset.induction_on with
    | empty => simp [z]
    | @insert i s hi ih =>
      have hz : z (insert i s) = Function.update (z s) i (y i) := by
        ext j
        by_cases hj : j = i
        · subst j; simp [z]
        · simp [z, hj]
      rw [hz]
      apply ih.trans
      apply coordinateMonotone_le_update (hv i)
      simpa [z, hi] using hxy i
  simpa only [z, Finset.mem_univ, ↓reduceIte] using hs Finset.univ

/-- A finite sequence of coordinate sorts gives a monotone rearrangement.
An invariant `P` may be carried through the sequence. -/
theorem exists_monotone_rearrangement_with {n : ℕ} {α : Type*} [LinearOrder α]
    (v : Cube n → α) (P : (Cube n → α) → Prop) (hv : P v)
    (hP : ∀ i w, P w → P (coordinateSort i w)) :
    ∃ w : Cube n → α, Monotone w ∧ P w ∧
      ∀ ψ : α → ℝ, cubeExpect (fun x => ψ (w x)) = cubeExpect (fun x => ψ (v x)) := by
  have hs (s : Finset (Fin n)) : ∃ w : Cube n → α,
      (∀ i ∈ s, CoordinateMonotone i w) ∧ P w ∧
      ∀ ψ : α → ℝ, cubeExpect (fun x => ψ (w x)) = cubeExpect (fun x => ψ (v x)) := by
    classical
    induction s using Finset.induction_on with
    | empty => exact ⟨v, by simp, hv, fun _ => rfl⟩
    | @insert i s hi ih =>
      obtain ⟨w, hw, hp, hd⟩ := ih
      refine ⟨coordinateSort i w, ?_, hP i w hp, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hjs
        · exact coordinateSort_monotone _ _
        · exact coordinateSort_preserves_monotone (by intro hij; subst j; exact hi hjs) (hw j hjs)
      · intro ψ
        rw [cubeExpect_coordinateSort, hd ψ]
  obtain ⟨w, hw, hp, hd⟩ := hs Finset.univ
  exact ⟨w, monotone_of_coordinateMonotone (fun i => hw i (Finset.mem_univ i)), hp, hd⟩

/-- Unconditional histogram-preserving monotone rearrangement in the same dimension.
This statement alone makes no information-improvement claim. -/
theorem exists_monotone_rearrangement {n : ℕ} {α : Type*} [LinearOrder α]
    (v : Cube n → α) : ∃ w : Cube n → α, Monotone w ∧
      ∀ ψ : α → ℝ, cubeExpect (fun x => ψ (w x)) = cubeExpect (fun x => ψ (v x)) := by
  obtain ⟨w, hw, _, hd⟩ := exists_monotone_rearrangement_with v (fun _ => True)
    trivial (fun _ _ _ => trivial)
  exact ⟨w, hw, hd⟩

/-- The BSC kernel on all coordinates other than `i`. -/
noncomputable def sectionKernel {n : ℕ} (i : Fin n) (r : ℝ) (x y : Cube n) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, if x j = y j then (1+r)/2 else (1-r)/2

/-- Noising the remaining coordinates of a fixed section. -/
noncomputable def sectionNoise {n : ℕ} (i : Fin n) (r : ℝ) (v : Cube n → ℝ)
    (y : Cube n) (b : Bool) : ℝ :=
  (∑ x, sectionKernel i r x y * v (Function.update x i b)) / 2

theorem sectionKernel_flip {n : ℕ} (i : Fin n) (r : ℝ) (x y : Cube n) :
    sectionKernel i r (cubeFlip i x) y = sectionKernel i r x y := by
  unfold sectionKernel
  apply Finset.prod_congr rfl
  intro j hj
  rw [cubeFlip_other i j x (Finset.mem_erase.mp hj).1]

theorem kernel_section {n : ℕ} (i : Fin n) (r : ℝ) (x y : Cube n) (b : Bool) :
    GeneralCK.noiseKernel ((1-r)/2) x (Function.update y i b) =
      (if x i = b then (1+r)/2 else (1-r)/2) * sectionKernel i r x y := by
  classical
  unfold GeneralCK.noiseKernel
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self, show 1-(1-r)/2 = (1+r)/2 by ring]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

/-- Exact decomposition into noising the other coordinates and then bit `i`. -/
theorem noise_section {n : ℕ} (i : Fin n) (r : ℝ) (v : Cube n → ℝ)
    (y : Cube n) (b : Bool) :
    noise r v (Function.update y i b) =
      ((1+r)/2) * sectionNoise i r v y b + ((1-r)/2) * sectionNoise i r v y (!b) := by
  have hp (x : Cube n) :
      GeneralCK.noiseKernel ((1-r)/2) x (Function.update y i b) * v x +
        GeneralCK.noiseKernel ((1-r)/2) (cubeFlip i x) (Function.update y i b) *
          v (cubeFlip i x) =
      ((1+r)/2) * (sectionKernel i r x y * v (Function.update x i b)) +
        ((1-r)/2) * (sectionKernel i r x y * v (Function.update x i (!b))) := by
    rw [kernel_section, kernel_section, sectionKernel_flip, cubeFlip_self]
    have hxself : Function.update x i (x i) = x := Function.update_eq_self i x
    cases hx : x i <;> cases b <;>
      simp_all only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
        Bool.true_eq_false, ↓reduceIte, cubeFlip] <;> ring
  have hf := Equiv.sum_comp (Function.Involutive.toPerm (cubeFlip i) (cubeFlip_involutive i))
    (fun x => GeneralCK.noiseKernel ((1-r)/2) x (Function.update y i b) * v x)
  change (∑ x, GeneralCK.noiseKernel ((1-r)/2) (cubeFlip i x)
    (Function.update y i b) * v (cubeFlip i x)) = noise r v (Function.update y i b) at hf
  have he := congrArg (fun q : Cube n → ℝ => ∑ x, q x) (funext hp)
  change (∑ x, (GeneralCK.noiseKernel ((1-r)/2) x (Function.update y i b) * v x +
      GeneralCK.noiseKernel ((1-r)/2) (cubeFlip i x) (Function.update y i b) * v (cubeFlip i x))) =
    ∑ x, (((1+r)/2) * (sectionKernel i r x y * v (Function.update x i b)) +
      ((1-r)/2) * (sectionKernel i r x y * v (Function.update x i (!b)))) at he
  rw [Finset.sum_add_distrib, hf, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at he
  change noise r v (Function.update y i b) + noise r v (Function.update y i b) = _ at he
  unfold sectionNoise
  linarith

theorem sectionKernel_nonneg {n : ℕ} (i : Fin n) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1)
    (x y : Cube n) : 0 ≤ sectionKernel i r x y := by
  apply Finset.prod_nonneg
  intro j _
  split_ifs <;> linarith

theorem sectionNoise_mono {n : ℕ} (i : Fin n) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1)
    {v w : Cube n → ℝ} {a b : Bool}
    (hvw : ∀ x, v (Function.update x i a) ≤ w (Function.update x i b)) (y : Cube n) :
    sectionNoise i r v y a ≤ sectionNoise i r w y b := by
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_mul_of_nonneg_left (hvw x) (sectionKernel_nonneg i hr₀ hr₁ x y)

theorem sectionNoise_sort_sum {n : ℕ} (i : Fin n) (r : ℝ) (v : Cube n → ℝ) (y : Cube n) :
    sectionNoise i r (coordinateSort i v) y false + sectionNoise i r (coordinateSort i v) y true =
      sectionNoise i r v y false + sectionNoise i r v y true := by
  simp only [sectionNoise, ← add_div, ← Finset.sum_add_distrib, ← mul_add]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  simp only [coordinateSort, Function.update_self, Bool.false_eq_true, ↓reduceIte,
    Function.update_idem, min_add_max]

theorem sectionNoise_sort_lower {n : ℕ} (i : Fin n) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1)
    (v : Cube n → ℝ) (y : Cube n) (b : Bool) :
    sectionNoise i r (coordinateSort i v) y false ≤ sectionNoise i r v y b := by
  apply sectionNoise_mono i hr₀ hr₁
  intro x
  simp only [coordinateSort, Function.update_self, Bool.false_eq_true, ↓reduceIte,
    Function.update_idem]
  cases b
  · exact min_le_left _ _
  · exact min_le_right _ _

/-- A convex function increases when a pair of fixed sum is spread apart. -/
theorem phi_pair_spread {a b c d : ℝ} (hc : c ∈ Set.Icc (-1) 1)
    (hd : d ∈ Set.Icc (-1) 1) (hca : c ≤ a) (had : a ≤ d)
    (he : a+b = c+d) : phi a + phi b ≤ phi c + phi d := by
  by_cases hcd : c = d
  · subst d
    have ha : a = c := le_antisymm had hca
    have hb : b = c := by linarith
    simp [ha, hb]
  · have hpos : 0 < d-c := by have : c ≤ d := hca.trans had; exact sub_pos.mpr (lt_of_le_of_ne this hcd)
    let t : ℝ := (d-a)/(d-c)
    have ht₀ : 0 ≤ t := div_nonneg (sub_nonneg.mpr had) hpos.le
    have ht₁ : t ≤ 1 := (div_le_one hpos).mpr (by linarith)
    have ha : t*c+(1-t)*d = a := by
      dsimp [t]
      field_simp
      ring
    have hb : (1-t)*c+t*d = b := by nlinarith [ha, he]
    have h₁ := phi_convexOn.2 hc hd ht₀ (sub_nonneg.mpr ht₁) (by ring : t+(1-t)=1)
    have h₂ := phi_convexOn.2 hc hd (sub_nonneg.mpr ht₁) ht₀ (by ring : (1-t)+t=1)
    simp only [smul_eq_mul, ha, hb] at h₁ h₂
    linarith

/-- Sorting preserves any closed interval containing the original field. -/
theorem coordinateSort_mem_Icc {n : ℕ} (i : Fin n) {v : Cube n → ℝ} {a b : ℝ}
    (hv : ∀ x, v x ∈ Set.Icc a b) (x : Cube n) : coordinateSort i v x ∈ Set.Icc a b := by
  unfold coordinateSort
  have h₀ := hv (Function.update x i false)
  have h₁ := hv (Function.update x i true)
  split_ifs
  · exact ⟨h₀.1.trans (le_max_left _ _), max_le h₀.2 h₁.2⟩
  · exact ⟨le_min h₀.1 h₁.1, (min_le_left _ _).trans h₀.2⟩

/-- Sorting spreads the paired noisy values apart while preserving their sum. -/
theorem noise_sort_pair {n : ℕ} (i : Fin n) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1)
    (v : Cube n → ℝ) (y : Cube n) :
    noise r (coordinateSort i v) (Function.update y i false) ≤ noise r v (Function.update y i false) ∧
    noise r v (Function.update y i false) ≤ noise r (coordinateSort i v) (Function.update y i true) ∧
    noise r v (Function.update y i false) + noise r v (Function.update y i true) =
      noise r (coordinateSort i v) (Function.update y i false) +
        noise r (coordinateSort i v) (Function.update y i true) := by
  have hs := sectionNoise_sort_sum i r v y
  have h₀ := sectionNoise_sort_lower i hr₀ hr₁ v y false
  have h₁ := sectionNoise_sort_lower i hr₀ hr₁ v y true
  simp only [noise_section, Bool.not_false, Bool.not_true]
  constructor
  · nlinarith [mul_nonneg hr₀ (sub_nonneg.mpr h₀)]
  constructor
  · nlinarith [mul_nonneg hr₀ (sub_nonneg.mpr h₁)]
  · nlinarith

theorem phi_noise_sort_pair {n : ℕ} (i : Fin n) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1)
    {v : Cube n → ℝ} (hv : ∀ x, v x ∈ Set.Icc (-1) 1) (y : Cube n) :
    phi (noise r v (Function.update y i false)) + phi (noise r v (Function.update y i true)) ≤
      phi (noise r (coordinateSort i v) (Function.update y i false)) +
        phi (noise r (coordinateSort i v) (Function.update y i true)) := by
  have hp := noise_sort_pair i hr₀ hr₁ v y
  exact phi_pair_spread
    (noise_mem_Icc (by linarith) hr₁ (coordinateSort_mem_Icc i hv) _)
    (noise_mem_Icc (by linarith) hr₁ (coordinateSort_mem_Icc i hv) _)
    hp.1 hp.2.1 hp.2.2

theorem cubeExpect_update_pair {n : ℕ} (i : Fin n) (v : Cube n → ℝ) :
    cubeExpect (fun x => v (Function.update x i false) + v (Function.update x i true)) =
      2 * cubeExpect v := by
  have hp (x : Cube n) : v (Function.update x i false) + v (Function.update x i true) =
      v x + v (cubeFlip i x) := by
    cases hx : x i
    · have hx₀ : Function.update x i false = x := by
        simpa only [hx] using Function.update_eq_self i x
      simp [cubeFlip, hx, hx₀]
    · have hx₁ : Function.update x i true = x := by
        simpa only [hx] using Function.update_eq_self i x
      simp [cubeFlip, hx, hx₁, add_comm]
  simp_rw [hp]
  rw [cubeExpect_add, cubeExpect_flip]
  ring

/-- Coordinate compression improves phi entropy after noise for every interval-valued field. -/
theorem phiEntropy_coordinateSort {n : ℕ} (i : Fin n) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1)
    {v : Cube n → ℝ} (hv : ∀ x, v x ∈ Set.Icc (-1) 1) :
    phiEntropy (noise r v) ≤ phiEntropy (noise r (coordinateSort i v)) := by
  have he := cubeExpect_mono (phi_noise_sort_pair i hr₀ hr₁ hv)
  rw [cubeExpect_update_pair i (fun x => phi (noise r v x)),
    cubeExpect_update_pair i (fun x => phi (noise r (coordinateSort i v) x))] at he
  have hm : cubeExpect (coordinateSort i v) = cubeExpect v := cubeExpect_coordinateSort i v id
  unfold phiEntropy
  rw [cubeExpect_noise, cubeExpect_noise, hm]
  linarith

theorem cubeSign_monotone : Monotone cubeSign := by
  intro a b hab
  cases a <;> cases b <;> norm_num [cubeSign]
  exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) hab)

theorem signField_coordinateSort {n : ℕ} (i : Fin n) (f : Cube n → Bool) :
    signField (coordinateSort i f) = coordinateSort i (signField f) := by
  ext x
  unfold signField coordinateSort
  split_ifs
  · exact cubeSign_monotone.map_max
  · exact cubeSign_monotone.map_min

/-- The local information-improvement inequality for Boolean coordinate sorting. -/
theorem information_coordinateSort {n : ℕ} (i : Fin n) (f : Cube n → Bool)
    {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    information f r ≤ information (coordinateSort i f) r := by
  rw [information_eq_phiEntropy, information_eq_phiEntropy, signField_coordinateSort]
  exact phiEntropy_coordinateSort i hr₀ hr₁ (signField_mem_Icc f)

/-- Local form of the coordinate-compression information inequality. -/
def CoordinateSortInformationImprovement (n : ℕ) : Prop :=
  ∀ (i : Fin n) (f : Cube n → Bool) (r : ℝ), 0 ≤ r → r ≤ 1 →
    information f r ≤ information (coordinateSort i f) r

/-- Generic reduction from a local compression inequality to simultaneous sorting. -/
theorem monotoneReduction_of_coordinateSortInformationImprovement {n : ℕ}
    (hc : CoordinateSortInformationImprovement n) (f : Cube n → Bool) :
    ∃ g : Cube n → Bool, Monotone g ∧
      cubeExpect (signField g) = cubeExpect (signField f) ∧
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 → information f r ≤ information g r := by
  obtain ⟨g, hg, hp, hd⟩ := exists_monotone_rearrangement_with f
    (fun g => ∀ r : ℝ, 0 ≤ r → r ≤ 1 → information f r ≤ information g r)
    (fun _ _ _ => le_rfl)
    (fun i g hg r hr₀ hr₁ => (hg r hr₀ hr₁).trans (hc i g r hr₀ hr₁))
  exact ⟨g, hg, hd cubeSign, hp⟩

/-- The manuscript's full monotone sorting lemma: same dimension and mean,
with simultaneous information improvement for every correlation in [0,1]. -/
theorem monotoneReduction {n : ℕ} (f : Cube n → Bool) :
    ∃ g : Cube n → Bool, Monotone g ∧
      cubeExpect (signField g) = cubeExpect (signField f) ∧
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 → information f r ≤ information g r := by
  apply monotoneReduction_of_coordinateSortInformationImprovement
  intro i f r hr₀ hr₁
  exact information_coordinateSort i f hr₀ hr₁

end MostInformativeBit
