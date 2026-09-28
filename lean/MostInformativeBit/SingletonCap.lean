import MostInformativeBit.RademacherMoments
import MostInformativeBit.EntropyContraction

/-! Singleton-energy bound of `source/fourier-cap.tex` and the balanced lift of `source/low.tex`.

Notation: `F = signField f` (values `±1`), `aᵢ = fourierCoeff F {i}`, `W = ∑ aᵢ²`.

* `section_bound`: `W ≤ aᵢ² + 1 - |aᵢ|` for every coordinate `i`
  (manuscript (elementary-singleton-section)).
* `singleton_cap`: `(∀ i, |aᵢ| ≤ 5/8) → W ≤ 49/64` (manuscript (elementary-fourier-cap)).
* `balanced_lift`: additionally `|E F| ≤ 5/8` gives `(E F)² + W ≤ 49/64`
  (low.tex (lift)), via `G(+1,x) = f x`, `G(-1,x) = ¬ f(¬x)` on one extra coordinate.
-/

namespace MostInformativeBit.SingletonCap

open MostInformativeBit MostInformativeBit.RademacherMoments
open scoped BigOperators

theorem character_singleton {n : ℕ} (i : Fin n) (x : Cube n) :
    character {i} x = cubeSign (x i) := by
  simp [character]

theorem cubeSign_abs (b : Bool) : |cubeSign b| = 1 := by
  cases b <;> norm_num [cubeSign]

theorem cubeExpect_comp_involutive {n : ℕ} (φ : Cube n → Cube n) (hφ : Function.Involutive φ)
    (g : Cube n → ℝ) : cubeExpect (fun x => g (φ x)) = cubeExpect g := by
  unfold cubeExpect
  congr 1
  exact Equiv.sum_comp (Function.Involutive.toPerm φ hφ) g

theorem abs_cubeExpect_le {n : ℕ} (v : Cube n → ℝ) :
    |cubeExpect v| ≤ cubeExpect (fun x => |v x|) := by
  rw [abs_le]
  constructor
  · have h := cubeExpect_mono (v := fun x => -1 * |v x|) (w := v)
      (fun x => by linarith [neg_abs_le (v x)])
    rw [cubeExpect_mul] at h
    linarith
  · exact cubeExpect_mono (fun x => le_abs_self _)

/-! ### Section bound -/

theorem section_bound {n : ℕ} (f : Cube n → Bool) (i : Fin n) :
    ∑ j, fourierCoeff (signField f) {j} ^ 2 ≤
      fourierCoeff (signField f) {i} ^ 2 + 1 - |fourierCoeff (signField f) {i}| := by
  classical
  set F := signField f with hF
  have inv : Function.Involutive (cubeFlip i) := cubeFlip_involutive i
  let s : Cube n → ℝ := fun x => (F x + F (cubeFlip i x)) / 2
  let d : Cube n → ℝ := fun x => (F x - F (cubeFlip i x)) / 2
  -- (1) off-coordinate coefficients of F and s agree
  have off : ∀ j, j ≠ i → fourierCoeff F {j} = fourierCoeff s {j} := by
    intro j hji
    have hflip := cubeExpect_comp_involutive (cubeFlip i) inv (fun x => F x * cubeSign (x j))
    simp only [cubeFlip_other _ _ _ hji] at hflip
    unfold fourierCoeff
    simp only [character_singleton]
    have e : (fun x => s x * cubeSign (x j)) = fun x =>
        (1/2) * (F x * cubeSign (x j)) + (1/2) * (F (cubeFlip i x) * cubeSign (x j)) := by
      funext x; simp only [s]; ring
    rw [e, cubeExpect_add, cubeExpect_mul, cubeExpect_mul, hflip]
    ring
  -- (2) |aᵢ| ≤ E|d|
  have hai : |fourierCoeff F {i}| ≤ cubeExpect (fun x => |d x|) := by
    have hflip := cubeExpect_comp_involutive (cubeFlip i) inv (fun x => F x * cubeSign (x i))
    simp only [cubeFlip_self, cubeSign_not] at hflip
    have ea : fourierCoeff F {i} = cubeExpect (fun x => d x * cubeSign (x i)) := by
      unfold fourierCoeff
      simp only [character_singleton]
      have e : (fun x => d x * cubeSign (x i)) = fun x =>
          (1/2) * (F x * cubeSign (x i)) + (1/2) * (F (cubeFlip i x) * -cubeSign (x i)) := by
        funext x; simp only [d]; ring
      rw [e, cubeExpect_add, cubeExpect_mul, cubeExpect_mul, hflip]
      ring
    rw [ea]
    refine le_trans (abs_cubeExpect_le _) (le_of_eq ?_)
    congr 1; funext x
    rw [abs_mul, cubeSign_abs, mul_one]
  -- (3) s² = 1 - |d| pointwise
  have hsd : ∀ x, s x ^ 2 = 1 - |d x| := by
    intro x
    simp only [s, d, hF, signField]
    cases f x <;> cases f (cubeFlip i x) <;> norm_num [cubeSign]
  have hEs : cubeExpect (fun x => s x ^ 2) ≤ 1 - |fourierCoeff F {i}| := by
    have : cubeExpect (fun x => s x ^ 2) = 1 - cubeExpect (fun x => |d x|) := by
      simp only [hsd]
      rw [cubeExpect_sub, cubeExpect_const]
    linarith
  -- (4) Bessel for s
  have bessel : ∑ j ∈ Finset.univ.erase i, fourierCoeff s {j} ^ 2 ≤
      cubeExpect (fun x => s x ^ 2) := by
    rw [parseval]
    calc ∑ j ∈ Finset.univ.erase i, fourierCoeff s {j} ^ 2
        ≤ ∑ j, fourierCoeff s {j} ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => sq_nonneg _)
      _ = ∑ S ∈ Finset.univ.image (fun j : Fin n => ({j} : Finset (Fin n))),
            fourierCoeff s S ^ 2 := by
          rw [Finset.sum_image (fun a _ b _ h => Finset.singleton_injective h)]
      _ ≤ ∑ S, fourierCoeff s S ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => sq_nonneg _)
  -- (5) assemble
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hsum : ∑ j ∈ Finset.univ.erase i, fourierCoeff F {j} ^ 2 =
      ∑ j ∈ Finset.univ.erase i, fourierCoeff s {j} ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [off j (Finset.ne_of_mem_erase hj)]
  rw [hsum]
  linarith

/-! ### Sign-sum link -/

theorem sqrt_energy_le {n : ℕ} (f : Cube n → Bool) (hW : 0 < ∑ j, fourierCoeff (signField f) {j} ^ 2) :
    let W := ∑ j, fourierCoeff (signField f) {j} ^ 2
    Real.sqrt W ≤ cubeExpect (fun x =>
      |signSum (fun j => fourierCoeff (signField f) {j} / Real.sqrt W) x|) := by
  intro W
  set a := fun j => fourierCoeff (signField f) {j}
  set b := fun j => a j / Real.sqrt W
  have hs : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW
  have hinner : cubeExpect (fun x => signField f x * signSum b x) = Real.sqrt W := by
    have e : (fun x => signField f x * signSum b x) =
        fun x => ∑ j, b j * (signField f x * character {j} x) := by
      funext x
      simp only [signSum, Finset.mul_sum, character_singleton]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [e, cubeExpect_sum]
    simp only [cubeExpect_mul]
    have : ∑ j, b j * cubeExpect (fun x => signField f x * character {j} x) =
        (∑ j, a j ^ 2) / Real.sqrt W := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl; intro j _
      simp only [b, a, fourierCoeff]; ring
    rw [this]
    have hW' : (∑ j, a j ^ 2) = W := rfl
    rw [hW', div_eq_iff hs.ne', ← sq, Real.sq_sqrt hW.le]
  rw [← hinner]
  apply cubeExpect_mono
  intro x
  calc signField f x * signSum b x ≤ |signField f x * signSum b x| := le_abs_self _
    _ = |signSum b x| := by rw [abs_mul, signField, cubeSign_abs, one_mul]

/-! ### The singleton-energy cap -/

/-- Manuscript (elementary-fourier-cap): all `|aᵢ| ≤ 5/8` ⇒ `W ≤ 49/64 = 1 - 5/8 + (5/8)²`. -/
theorem singleton_cap {n : ℕ} (f : Cube n → Bool)
    (ha : ∀ i, |fourierCoeff (signField f) {i}| ≤ 5/8) :
    ∑ i, fourierCoeff (signField f) {i} ^ 2 ≤ 49/64 := by
  set a := fun j => fourierCoeff (signField f) {j} with ha_def
  by_cases hA : ∃ i, 3/8 ≤ |a i|
  · obtain ⟨i, hi⟩ := hA
    have hs := section_bound f i
    have hx := ha i
    have hsq : a i ^ 2 = |a i| ^ 2 := (sq_abs _).symm
    change ∑ j, a j ^ 2 ≤ a i ^ 2 + 1 - |a i| at hs
    change ∑ j, a j ^ 2 ≤ 49/64
    rw [hsq] at hs
    nlinarith
  · push Not at hA
    by_contra hW
    push Not at hW
    set W := ∑ j, fourierCoeff (signField f) {j} ^ 2 with hWdef
    have hWpos : 0 < W := by linarith
    have hs : 0 < Real.sqrt W := Real.sqrt_pos.mpr hWpos
    set b := fun j => fourierCoeff (signField f) {j} / Real.sqrt W
    have hb2 : powerSum b 2 = 1 := by
      unfold powerSum
      simp only [b, div_pow, Real.sq_sqrt hWpos.le, ← Finset.sum_div]
      exact div_self hWpos.ne'
    have hbmax : ∀ j, b j ^ 2 ≤ 1/5 := by
      intro j
      simp only [b, div_pow, Real.sq_sqrt hWpos.le]
      rw [div_le_iff₀ hWpos]
      have h1 := hA j
      have h2 : fourierCoeff (signField f) {j} ^ 2 < 9/64 := by
        rw [← sq_abs]; nlinarith [abs_nonneg (a j)]
      linarith
    have hlt := signSum_abs_lt b hb2 hbmax
    have hle := sqrt_energy_le f hWpos
    have hsq : Real.sqrt W < 7/8 := lt_of_le_of_lt hle hlt
    have : W < 49/64 := by
      have := Real.sq_sqrt hWpos.le
      nlinarith
    linarith

/-! ### Balanced lift (low.tex (lift)) -/

/-- Global negation of all coordinates. -/
def cubeNeg {n : ℕ} (x : Cube n) : Cube n := fun j => !(x j)

theorem cubeNeg_involutive {n : ℕ} : Function.Involutive (cubeNeg (n := n)) := by
  intro x; funext j; simp [cubeNeg]

/-- The balanced lift `G(+1,x) = f x`, `G(-1,x) = ¬ f(¬x)` on `Cube (n+1)`. -/
def balancedLift {n : ℕ} (f : Cube n → Bool) (y : Cube (n+1)) : Bool :=
  if y 0 then f (Fin.tail y) else !(f (cubeNeg (Fin.tail y)))

theorem lift_cons_true {n : ℕ} (f : Cube n → Bool) (x : Cube n) :
    signField (balancedLift f) (Fin.cons true x) = signField f x := by
  simp [balancedLift, signField]

theorem lift_cons_false {n : ℕ} (f : Cube n → Bool) (x : Cube n) :
    signField (balancedLift f) (Fin.cons false x) = -signField f (cubeNeg x) := by
  simp [balancedLift, signField, cubeSign_not]

theorem lift_coeff_zero {n : ℕ} (f : Cube n → Bool) :
    fourierCoeff (signField (balancedLift f)) {0} = cubeExpect (signField f) := by
  unfold fourierCoeff
  simp only [character_singleton]
  rw [cubeExpect_succ]
  simp only [Fin.cons_zero, lift_cons_true, lift_cons_false, cubeSign, Bool.false_eq_true,
    if_false, if_true, mul_one, mul_neg, neg_neg]
  have h := cubeExpect_comp_involutive cubeNeg cubeNeg_involutive (signField f)
  rw [h]
  ring

theorem lift_coeff_succ {n : ℕ} (f : Cube n → Bool) (j : Fin n) :
    fourierCoeff (signField (balancedLift f)) {j.succ} = fourierCoeff (signField f) {j} := by
  unfold fourierCoeff
  simp only [character_singleton]
  rw [cubeExpect_succ]
  simp only [Fin.cons_succ, lift_cons_true, lift_cons_false]
  have h := cubeExpect_comp_involutive cubeNeg cubeNeg_involutive
    (fun x => signField f x * cubeSign (x j))
  have h' : cubeExpect (fun x => -signField f (cubeNeg x) * cubeSign (x j)) =
      cubeExpect (fun x => signField f x * cubeSign (x j)) := by
    rw [← h]
    congr 1
    funext x
    simp only [cubeNeg, cubeSign_not]
    ring
  rw [h']
  ring

/-- low.tex (lift): with all singleton coefficients and the mean bounded by `5/8`,
`m² + W₁(f) = W₁(G) ≤ 49/64`, where `m = E F`. -/
theorem balanced_lift {n : ℕ} (f : Cube n → Bool)
    (ha : ∀ i, |fourierCoeff (signField f) {i}| ≤ 5/8)
    (hm : |cubeExpect (signField f)| ≤ 5/8) :
    cubeExpect (signField f) ^ 2 + ∑ i, fourierCoeff (signField f) {i} ^ 2 ≤ 49/64 := by
  have hG : ∀ i, |fourierCoeff (signField (balancedLift f)) {i}| ≤ 5/8 := by
    intro i
    refine Fin.cases (motive := fun i => |fourierCoeff (signField (balancedLift f)) {i}| ≤ 5/8)
      ?_ ?_ i
    · rw [lift_coeff_zero]; exact hm
    · intro j; rw [lift_coeff_succ]; exact ha j
  have hcap := singleton_cap (balancedLift f) hG
  rw [Fin.sum_univ_succ, lift_coeff_zero] at hcap
  simp only [lift_coeff_succ] at hcap
  exact hcap

end MostInformativeBit.SingletonCap
