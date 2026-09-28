import MostInformativeBit.CubeFourier
import MostInformativeBit.MomentMajorant

/-! Independent-sign moments and the sign-sum bound of `source/fourier-cap.tex`.

* `moments`: for `Z = ∑ bᵢ Xᵢ` with independent uniform signs on the actual cube,
  `E Z^k = momentFormula (powerSum b) k` for every `k ≤ 10` (odd moments vanish). Proved by
  induction on the dimension via the product structure `Cube (n+1) ≃ Bool × Cube n`.
* `power_constraints`: `∑ bᵢ² = 1`, `max bᵢ² ≤ 1/5` give `0 ≤ σ₄ ≤ 1/5`, `σ₆ ≤ σ₄/5`,
  `σ₈ ≥ σ₄³`, `σ₁₀ ≤ σ₈/5`.
* `signSum_abs_lt`: under the same hypotheses `E|Z| < 7/8` (manuscript (elementary-sign-sum)),
  using the coordinator's `MomentMajorant`.
-/

namespace MostInformativeBit.RademacherMoments

open MostInformativeBit
open scoped BigOperators

noncomputable def signSum {n : ℕ} (b : Fin n → ℝ) (x : Cube n) : ℝ := ∑ i, b i * cubeSign (x i)

noncomputable def powerSum {n : ℕ} (b : Fin n → ℝ) (j : ℕ) : ℝ := ∑ i, b i ^ j

/-- Moments of a Rademacher sum in terms of power sums `q j = ∑ bᵢ^j`. -/
noncomputable def momentFormula (q : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1
  else if k = 2 then q 2
  else if k = 4 then 3 * q 2 ^ 2 - 2 * q 4
  else if k = 6 then 15 * q 2 ^ 3 - 30 * q 2 * q 4 + 16 * q 6
  else if k = 8 then 105 * q 2 ^ 4 - 420 * q 2 ^ 2 * q 4 + 448 * q 2 * q 6 + 140 * q 4 ^ 2
    - 272 * q 8
  else if k = 10 then 7936 * q 10 + 945 * q 2 ^ 5 - 6300 * q 2 ^ 3 * q 4
    + 10080 * q 2 ^ 2 * q 6 + 6300 * q 2 * q 4 ^ 2 - 12240 * q 2 * q 8 - 6720 * q 4 * q 6
  else 0

/-! ### Product structure of the cube -/

theorem cubeExpect_succ {n : ℕ} (g : Cube (n+1) → ℝ) :
    cubeExpect g = (cubeExpect (fun x : Cube n => g (Fin.cons false x)) +
      cubeExpect (fun x : Cube n => g (Fin.cons true x))) / 2 := by
  unfold cubeExpect
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => Bool)) g,
    Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, GeneralCK.Information.cubeWeight, zpow_neg,
    zpow_natCast, pow_succ]
  ring

theorem signSum_cons {n : ℕ} (c : ℝ) (b : Fin n → ℝ) (s : Bool) (x : Cube n) :
    signSum (Fin.cons c b : Fin (n+1) → ℝ) (Fin.cons s x) = c * cubeSign s + signSum b x := by
  simp [signSum, Fin.sum_univ_succ]

theorem powerSum_cons {n : ℕ} (c : ℝ) (b : Fin n → ℝ) (j : ℕ) :
    powerSum (Fin.cons c b : Fin (n+1) → ℝ) j = c ^ j + powerSum b j := by
  simp [powerSum, Fin.sum_univ_succ]

theorem expect_shift_pow {n : ℕ} (b : Fin n → ℝ) (y : ℝ) (k : ℕ) :
    cubeExpect (fun x => (y + signSum b x) ^ k) =
      ∑ j ∈ Finset.range (k+1), (y ^ (k-j) * (k.choose j : ℝ)) *
        cubeExpect (fun x => signSum b x ^ j) := by
  have : (fun x => (y + signSum b x) ^ k) = fun x => ∑ j ∈ Finset.range (k+1),
      (y ^ (k-j) * (k.choose j : ℝ)) * signSum b x ^ j := by
    funext x
    rw [add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [this, cubeExpect_sum]
  simp only [cubeExpect_mul]

/-- One-coordinate moment recursion. -/
theorem moment_cons {n : ℕ} (c : ℝ) (b : Fin n → ℝ) (k : ℕ) :
    cubeExpect (fun x => signSum (Fin.cons c b : Fin (n+1) → ℝ) x ^ k) =
      ∑ j ∈ Finset.range (k+1), (k.choose j : ℝ) *
        cubeExpect (fun x => signSum b x ^ j) * ((c ^ (k-j) + (-c) ^ (k-j)) / 2) := by
  rw [cubeExpect_succ]
  simp only [signSum_cons, cubeSign]
  simp only [Bool.false_eq_true, if_false, if_true, mul_neg, mul_one]
  rw [expect_shift_pow, expect_shift_pow, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Rademacher moments through degree 10, on the actual finite cube. -/
theorem moments (n : ℕ) : ∀ (b : Fin n → ℝ) (k : ℕ), k ≤ 10 →
    cubeExpect (fun x => signSum b x ^ k) = momentFormula (powerSum b) k := by
  induction n with
  | zero =>
    intro b k hk
    have hz : ∀ x : Cube 0, signSum b x = 0 := fun x => by simp [signSum]
    have hp : ∀ j, powerSum b j = 0 := fun j => by simp [powerSum]
    simp only [hz]
    interval_cases k <;> simp [momentFormula, hp]
  | succ n ih =>
    intro b k hk
    obtain ⟨c, b', rfl⟩ : ∃ c b', b = (Fin.cons c b' : Fin (n+1) → ℝ) :=
      ⟨b 0, Fin.tail b, (Fin.cons_self_tail b).symm⟩
    rw [moment_cons]
    rw [Finset.sum_congr rfl (fun j hj => by
      rw [ih b' j (by linarith [Finset.mem_range.1 hj])])]
    interval_cases k <;>
      simp [Finset.sum_range_succ, momentFormula, powerSum_cons, Nat.choose] <;> ring

/-! ### Power-sum constraints -/

theorem power_constraints {n : ℕ} (b : Fin n → ℝ) (h2 : powerSum b 2 = 1)
    (hmax : ∀ i, b i ^ 2 ≤ 1/5) :
    0 ≤ powerSum b 4 ∧ powerSum b 4 ≤ 1/5 ∧ powerSum b 6 ≤ powerSum b 4 / 5 ∧
      powerSum b 4 ^ 3 ≤ powerSum b 8 ∧ powerSum b 10 ≤ powerSum b 8 / 5 := by
  have hsq : ∀ i, 0 ≤ b i ^ 2 := fun i => sq_nonneg _
  -- b^(2k+2) = b^(2k) * b^2 ≤ b^(2k)/5
  have step : ∀ k : ℕ, powerSum b (2*k+2) ≤ powerSum b (2*k) / 5 := by
    intro k
    unfold powerSum
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro i _
    have e : b i ^ (2*k+2) = b i ^ (2*k) * b i ^ 2 := by rw [pow_add]
    have h0 : 0 ≤ b i ^ (2*k) := by rw [pow_mul]; positivity
    rw [e]
    nlinarith [hmax i]
  have p4n : 0 ≤ powerSum b 4 := Finset.sum_nonneg (fun i _ => by positivity)
  have p6n : 0 ≤ powerSum b 6 := Finset.sum_nonneg (fun i _ => by positivity)
  have p8n : 0 ≤ powerSum b 8 := Finset.sum_nonneg (fun i _ => by positivity)
  have s4 := step 1
  have s6 := step 2
  have s10 := step 4
  norm_num at s4 s6 s10
  rw [h2] at s4
  -- Cauchy–Schwarz twice
  have cs1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => b i) (fun i => b i ^ 3)
  have cs2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => b i ^ 2) (fun i => b i ^ 4)
  have e1 : (∑ i, b i * b i ^ 3) = powerSum b 4 := by
    unfold powerSum; apply Finset.sum_congr rfl; intro i _; ring
  have e2 : (∑ i, (b i ^ 3) ^ 2) = powerSum b 6 := by
    unfold powerSum; apply Finset.sum_congr rfl; intro i _; ring
  have e3 : (∑ i, b i ^ 2 * b i ^ 4) = powerSum b 6 := by
    unfold powerSum; apply Finset.sum_congr rfl; intro i _; ring
  have e4 : (∑ i, (b i ^ 2) ^ 2) = powerSum b 4 := by
    unfold powerSum; apply Finset.sum_congr rfl; intro i _; ring
  have e5 : (∑ i, (b i ^ 4) ^ 2) = powerSum b 8 := by
    unfold powerSum; apply Finset.sum_congr rfl; intro i _; ring
  have e6 : (∑ i, b i ^ 2) = powerSum b 2 := rfl
  simp only [e1, e2, e6, h2, one_mul] at cs1
  simp only [e3, e4, e5] at cs2
  -- σ₄² ≤ σ₆, σ₆² ≤ σ₄σ₈ ⇒ σ₄⁴ ≤ σ₄σ₈ ⇒ σ₄³ ≤ σ₈
  have h44 : powerSum b 4 ^ 4 ≤ powerSum b 4 * powerSum b 8 := by
    have : (powerSum b 4 ^ 2) ^ 2 ≤ powerSum b 6 ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) cs1 2
    nlinarith
  have h3 : powerSum b 4 ^ 3 ≤ powerSum b 8 := by
    rcases eq_or_lt_of_le p4n with e | hp
    · rw [← e]; simpa using p8n
    · have : powerSum b 4 * powerSum b 4 ^ 3 ≤ powerSum b 4 * powerSum b 8 := by
        nlinarith
      exact le_of_mul_le_mul_left this hp
  exact ⟨p4n, by linarith, s6, h3, s10⟩

/-! ### The sign-sum bound -/

theorem cubeExpect_even_poly {n : ℕ} (Z : Cube n → ℝ) (c0 c1 c2 c3 c4 c5 : ℝ) :
    cubeExpect (fun x => c0 + c1 * Z x ^ 2 + c2 * Z x ^ 4 + c3 * Z x ^ 6 + c4 * Z x ^ 8 +
      c5 * Z x ^ 10) =
    c0 + c1 * cubeExpect (fun x => Z x ^ 2) + c2 * cubeExpect (fun x => Z x ^ 4) +
      c3 * cubeExpect (fun x => Z x ^ 6) + c4 * cubeExpect (fun x => Z x ^ 8) +
      c5 * cubeExpect (fun x => Z x ^ 10) := by
  simp only [cubeExpect_add, cubeExpect_mul, cubeExpect_const]

/-- Manuscript (elementary-sign-sum): `∑ bᵢ² = 1`, `max bᵢ² ≤ 1/5` ⇒ `E|∑ bᵢXᵢ| < 7/8`. -/
theorem signSum_abs_lt {n : ℕ} (b : Fin n → ℝ) (h2 : powerSum b 2 = 1)
    (hmax : ∀ i, b i ^ 2 ≤ 1/5) :
    cubeExpect (fun x => |signSum b x|) < 7/8 := by
  obtain ⟨t0, t1, h6, h8, h10⟩ := power_constraints b h2 hmax
  have hmaj : cubeExpect (fun x => |signSum b x|) ≤
      cubeExpect (fun x => momentMajorant (signSum b x ^ 2)) :=
    cubeExpect_mono (fun x => abs_le_momentMajorant _)
  have hpoly : (fun x => momentMajorant (signSum b x ^ 2)) = fun x =>
      1260006516 / 4042912500 + 3660186285 / 4042912500 * signSum b x ^ 2 +
      (-1008169920) / 4042912500 * signSum b x ^ 4 + 191446315 / 4042912500 * signSum b x ^ 6 +
      (-17928800) / 4042912500 * signSum b x ^ 8 + 637696 / 4042912500 * signSum b x ^ 10 := by
    funext x
    unfold momentMajorant momentNumerator
    ring
  have hval : cubeExpect (fun x => momentMajorant (signSum b x ^ 2)) =
      momentExpression (powerSum b 4) (powerSum b 6) (powerSum b 8) (powerSum b 10) /
        4042912500 := by
    rw [hpoly, cubeExpect_even_poly]
    rw [moments n b 2 (by norm_num), moments n b 4 (by norm_num), moments n b 6 (by norm_num),
      moments n b 8 (by norm_num), moments n b 10 (by norm_num)]
    simp only [momentFormula]
    norm_num
    rw [h2]
    unfold momentExpression
    ring
  have hlt := momentExpression_lt_seven_eighths t0 t1 h6 h8 h10
  linarith

end MostInformativeBit.RademacherMoments
