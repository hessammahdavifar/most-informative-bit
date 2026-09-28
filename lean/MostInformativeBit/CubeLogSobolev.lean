import MostInformativeBit.EntropyTensorization

/-! Unconditional Gross log-Sobolev inequality on the uniform cube, in the
normalization `L chi_S = |S| chi_S` of `cubeLaplacian`:
`cubeEntropy (w^2) ≤ 2 * cubeExpect (w * cubeLaplacian w)` for every real field.

Route: the sharp two-point inequality (power series of the logarithm),
Cauchy-Schwarz, and the entropy chain rule `cubeEntropy_succ`, by induction on
the dimension. The pivotal estimate of mechanism.tex follows from Gibbs. -/
namespace MostInformativeBit
open scoped BigOperators
open Real

/-! ### Two-point Gross inequality -/

/-- Normalized two-point Gross defect: entropy of `(1+s)^2, (1-s)^2`. -/
noncomputable def grossG (s : ℝ) : ℝ := pairEntropy ((1+s)^2) ((1-s)^2)

theorem grossG_eq {s : ℝ} (hs : |s| < 1) :
    grossG s = 2*s*(log (1+s) - log (1-s)) - (1+s^2)*(log (1+s^2) - log (1-s^2)) := by
  have hp : 0 < 1 + s := by linarith [neg_abs_le s]
  have hm : 0 < 1 - s := by linarith [le_abs_self s]
  unfold grossG pairEntropy
  rw [show ((1+s)^2 + (1-s)^2)/2 = 1+s^2 by ring, Real.log_pow, Real.log_pow,
    show 1 - s^2 = (1+s)*(1-s) by ring, Real.log_mul hp.ne' hm.ne']
  push_cast
  ring

theorem grossG_le {s : ℝ} (hs : |s| < 1) : grossG s ≤ 2 * s^2 := by
  set x := s^2 with hx
  have hx0 : 0 ≤ x := sq_nonneg s
  have hx1 : x < 1 := by rw [hx, sq_lt_one_iff_abs_lt_one]; exact hs
  have hxa : |x| < 1 := by rwa [abs_of_nonneg hx0]
  -- the two logarithmic series
  set a : ℕ → ℝ := fun k => 2*s * (2 * (1 / (2*(k:ℝ)+1)) * s^(2*k+1)) with ha
  have hA : HasSum a (2*s*(log (1+s) - log (1-s))) :=
    (Real.hasSum_log_sub_log_of_abs_lt_one hs).mul_left (2*s)
  have hB := (Real.hasSum_log_sub_log_of_abs_lt_one hxa).mul_left (1+x)
  have he : Summable (fun k => a (2*k)) :=
    hA.summable.comp_injective (mul_right_injective₀ (two_ne_zero))
  have ho : Summable (fun k => a (2*k+1)) :=
    hA.summable.comp_injective (fun i j h => by simpa using h)
  have hsplit := tsum_even_add_odd he ho
  rw [hA.tsum_eq] at hsplit
  have hf := (he.hasSum.add ho.hasSum).sub hB
  rw [hsplit, ← grossG_eq hs] at hf
  -- regroup: positive part P, negative part Q
  set P : ℕ → ℝ := fun j => 2 / ((4*(j:ℝ)+1)*(2*j+1)) * x^(2*j+1) with hP
  set Q : ℕ → ℝ := fun j => 2 / ((4*(j:ℝ)+3)*(2*j+1)) * x^(2*j+2) with hQ
  have hterm : ∀ j : ℕ, a (2*j) + a (2*j+1) - (1+x) * (2 * (1 / (2*(j:ℝ)+1)) * x^(2*j+1)) =
      P j - Q j := by
    intro j
    have h1 : (0:ℝ) < 4*j+1 := by positivity
    have h2 : (0:ℝ) < 4*j+3 := by positivity
    have h3 : (0:ℝ) < 2*j+1 := by positivity
    simp only [ha, hP, hQ, hx]
    push_cast
    field_simp
    ring
  have hf' : HasSum (fun j => P j - Q j) (grossG s) := by
    have : (fun j => a (2*j) + a (2*j+1) - (1+x) * (2 * (1 / (2*(j:ℝ)+1)) * x^(2*j+1))) =
        fun j => P j - Q j := funext hterm
    rw [← this]; exact hf
  have hgeom := summable_geometric_of_lt_one hx0 hx1
  have hQs : Summable Q := by
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hgeom
    · simp only [hQ]; positivity
    · simp only [hQ]
      have hc : 2 / ((4*(j:ℝ)+3)*(2*j+1)) ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
      have hp : x^(2*j+2) ≤ x^j := pow_le_pow_of_le_one hx0 hx1.le (by omega)
      calc 2 / ((4*(j:ℝ)+3)*(2*j+1)) * x^(2*j+2) ≤ 1 * x^j :=
            mul_le_mul hc hp (by positivity) zero_le_one
        _ = x^j := one_mul _
  have hPs : Summable P := by
    have := hf'.summable.add hQs
    simpa using this
  have hG : grossG s = ∑' j, P j - ∑' j, Q j := by
    rw [← hf'.tsum_eq, hPs.tsum_sub hQs]
  have hP0 : P 0 = 2 * x := by simp [hP]
  have hPsplit := hPs.tsum_eq_zero_add
  rw [hP0] at hPsplit
  have hPs1 : Summable (fun j => P (j+1)) := (summable_nat_add_iff 1).2 hPs
  have hdiff : 0 ≤ ∑' j, (Q j - P (j+1)) := by
    apply tsum_nonneg
    intro j
    simp only [hP, hQ]
    push_cast
    have hc : 2 / ((4*((j:ℝ)+1)+1)*(2*((j:ℝ)+1)+1)) ≤ 2 / ((4*(j:ℝ)+3)*(2*j+1)) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
    have hp : x^(2*(j+1)+1) ≤ x^(2*j+2) := pow_le_pow_of_le_one hx0 hx1.le (by omega)
    have := mul_le_mul hc hp (by positivity) (by positivity)
    linarith
  rw [hQs.tsum_sub hPs1] at hdiff
  rw [hG, hPsplit]
  linarith

theorem pairEntropy_smul {c u v : ℝ} (hc : 0 < c) (hu : 0 < u) (hv : 0 < v) :
    pairEntropy (c*u) (c*v) = c * pairEntropy u v := by
  unfold pairEntropy
  rw [show (c*u + c*v)/2 = c*((u+v)/2) by ring, Real.log_mul hc.ne' hu.ne',
    Real.log_mul hc.ne' hv.ne', Real.log_mul hc.ne' (by positivity)]
  ring

theorem pairEntropy_sq_zero (a : ℝ) : pairEntropy (a^2) 0 ≤ a^2/2 := by
  rcases eq_or_ne a 0 with h | h
  · subst h; simp [pairEntropy]
  have ha : 0 < a^2 := by positivity
  have hval : pairEntropy (a^2) 0 = a^2/2 * log 2 := by
    unfold pairEntropy
    simp only [zero_mul, add_zero]
    rw [Real.log_div ha.ne' two_ne_zero]
    ring
  rw [hval]
  have := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 2) (by norm_num)
  nlinarith

/-- Sharp two-point Gross inequality: `Ent(g^2) ≤ 2 E[g Lg] = (a-b)^2/2`. -/
theorem pairEntropy_sq_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    pairEntropy (a^2) (b^2) ≤ (a-b)^2/2 := by
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · set M := (a+b)/2 with hM
      set s := (a-b)/(a+b) with hsdef
      have hab : 0 < a + b := by positivity
      have hM0 : 0 < M := by positivity
      have hs : |s| < 1 := by
        rw [abs_lt, hsdef]
        constructor
        · rw [lt_div_iff₀ hab]; linarith
        · rw [div_lt_iff₀ hab]; linarith
      have hp : 0 < 1 + s := by linarith [neg_abs_le s]
      have hm : 0 < 1 - s := by linarith [le_abs_self s]
      have ea : a^2 = M^2 * (1+s)^2 := by rw [hM, hsdef]; field_simp; ring
      have eb : b^2 = M^2 * (1-s)^2 := by rw [hM, hsdef]; field_simp; ring
      have ed : (a-b)^2/2 = M^2 * (2*s^2) := by rw [hM, hsdef]; field_simp
      rw [ea, eb, ed, pairEntropy_smul (by positivity) (by positivity) (by positivity)]
      exact mul_le_mul_of_nonneg_left (grossG_le hs) (by positivity)
    · subst hb'
      simpa using pairEntropy_sq_zero a
  · subst ha'
    have h := pairEntropy_sq_zero b
    have hsym : pairEntropy 0 (b^2) = pairEntropy (b^2) 0 := by
      unfold pairEntropy; ring_nf
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    rw [hsym]
    simpa using h

/-! ### Laplacian and Dirichlet form under the first-coordinate split -/

theorem cubeFlip_zero_cons {n : ℕ} (b : Bool) (y : Cube n) :
    cubeFlip 0 (Fin.cons b y : Cube (n+1)) = Fin.cons (!b) y := by
  simp [cubeFlip, Fin.update_cons_zero]

theorem cubeFlip_succ_cons {n : ℕ} (i : Fin n) (b : Bool) (y : Cube n) :
    cubeFlip i.succ (Fin.cons b y : Cube (n+1)) = Fin.cons b (cubeFlip i y) := by
  simp [cubeFlip, Fin.cons_update]

theorem cubeLaplacian_cons {n : ℕ} (w : Cube (n+1) → ℝ) (b : Bool) (y : Cube n) :
    cubeLaplacian w (Fin.cons b y) =
      (w (Fin.cons b y) - w (Fin.cons (!b) y)) / 2 +
        cubeLaplacian (fun z : Cube n => w (Fin.cons b z)) y := by
  simp only [cubeLaplacian, Fin.sum_univ_succ, cubeDerivative, cubeFlip_zero_cons,
    cubeFlip_succ_cons]

theorem dirichlet_succ {n : ℕ} (w : Cube (n+1) → ℝ) :
    cubeExpect (fun x => w x * cubeLaplacian w x) =
      (cubeExpect (fun y : Cube n => (w (Fin.cons false y) - w (Fin.cons true y))^2) / 2 +
        cubeExpect (fun y : Cube n => w (Fin.cons false y) *
          cubeLaplacian (fun z : Cube n => w (Fin.cons false z)) y) +
        cubeExpect (fun y : Cube n => w (Fin.cons true y) *
          cubeLaplacian (fun z : Cube n => w (Fin.cons true z)) y)) / 2 := by
  rw [cubeExpect_succ]
  simp only [cubeLaplacian_cons, Bool.not_false, Bool.not_true]
  have h0 : (fun y : Cube n => w (Fin.cons false y) *
      ((w (Fin.cons false y) - w (Fin.cons true y)) / 2 +
        cubeLaplacian (fun z : Cube n => w (Fin.cons false z)) y)) =
      fun y => (1/2) * (w (Fin.cons false y) * (w (Fin.cons false y) - w (Fin.cons true y))) +
        w (Fin.cons false y) * cubeLaplacian (fun z : Cube n => w (Fin.cons false z)) y := by
    funext y; ring
  have h1 : (fun y : Cube n => w (Fin.cons true y) *
      ((w (Fin.cons true y) - w (Fin.cons false y)) / 2 +
        cubeLaplacian (fun z : Cube n => w (Fin.cons true z)) y)) =
      fun y => (1/2) * (w (Fin.cons true y) * (w (Fin.cons true y) - w (Fin.cons false y))) +
        w (Fin.cons true y) * cubeLaplacian (fun z : Cube n => w (Fin.cons true z)) y := by
    funext y; ring
  have hsq : (fun y : Cube n => (w (Fin.cons false y) - w (Fin.cons true y))^2) =
      fun y => w (Fin.cons false y) * (w (Fin.cons false y) - w (Fin.cons true y)) +
        w (Fin.cons true y) * (w (Fin.cons true y) - w (Fin.cons false y)) := by
    funext y; ring
  rw [h0, h1, hsq, cubeExpect_add, cubeExpect_add, cubeExpect_add, cubeExpect_mul,
    cubeExpect_mul]
  ring

/-! ### Cauchy-Schwarz for the uniform average -/

theorem cubeExpect_mul_le_sqrt {n : ℕ} (u v : Cube n → ℝ) :
    cubeExpect (fun x => u x * v x) ≤
      √(cubeExpect (fun x => u x ^ 2)) * √(cubeExpect (fun x => v x ^ 2)) := by
  have hw : 0 < GeneralCK.Information.cubeWeight n := by
    unfold GeneralCK.Information.cubeWeight; positivity
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  have hsq : cubeExpect (fun x => u x * v x) ^ 2 ≤
      cubeExpect (fun x => u x ^ 2) * cubeExpect (fun x => v x ^ 2) := by
    simp only [cubeExpect, mul_pow]
    have := mul_le_mul_of_nonneg_left hcs (sq_nonneg (GeneralCK.Information.cubeWeight n))
    nlinarith
  rw [← Real.sqrt_mul (cubeExpect_nonneg (fun x => sq_nonneg (u x)))]
  exact (le_abs_self _).trans (Real.abs_le_sqrt hsq)

/-! ### Gross inequality by tensorization -/

theorem cubeLaplacian_dim_zero (v : Cube 0 → ℝ) (x : Cube 0) : cubeLaplacian v x = 0 := by
  simp [cubeLaplacian]

/-- Gross log-Sobolev inequality on the uniform cube, every dimension and every
real field (nonnegativity is not needed). -/
theorem gross_logSobolev : ∀ {n : ℕ} (w : Cube n → ℝ),
    cubeEntropy (fun x => w x ^ 2) ≤ 2 * cubeExpect (fun x => w x * cubeLaplacian w x) := by
  intro n
  induction n with
  | zero => intro w; simp [cubeEntropy_dim_zero, cubeLaplacian_dim_zero]
  | succ n ih =>
    intro w
    set w0 : Cube n → ℝ := fun y => w (Fin.cons false y) with hw0
    set w1 : Cube n → ℝ := fun y => w (Fin.cons true y) with hw1
    have hi0 := ih w0
    have hi1 := ih w1
    rw [cubeEntropy_succ (fun x => w x ^ 2), dirichlet_succ w]
    set A := cubeExpect (fun y => w0 y ^ 2) with hA
    set B := cubeExpect (fun y => w1 y ^ 2) with hB
    have hA0 : 0 ≤ A := cubeExpect_nonneg (fun y => sq_nonneg _)
    have hB0 : 0 ≤ B := cubeExpect_nonneg (fun y => sq_nonneg _)
    have hpair := pairEntropy_sq_le (Real.sqrt_nonneg A) (Real.sqrt_nonneg B)
    rw [Real.sq_sqrt hA0, Real.sq_sqrt hB0] at hpair
    have hcs := cubeExpect_mul_le_sqrt w0 w1
    have hdiff : cubeExpect (fun y => (w0 y - w1 y)^2) =
        A + B - 2 * cubeExpect (fun y => w0 y * w1 y) := by
      rw [hA, hB, ← cubeExpect_mul, ← cubeExpect_add, ← cubeExpect_sub]
      congr 1; funext y; ring
    have hAB : (√A - √B)^2 ≤ cubeExpect (fun y => (w0 y - w1 y)^2) := by
      rw [hdiff]
      have := Real.sq_sqrt hA0
      have := Real.sq_sqrt hB0
      nlinarith
    show pairEntropy A B + (cubeEntropy (fun y => w0 y ^ 2) +
        cubeEntropy (fun y => w1 y ^ 2)) / 2 ≤ _
    linarith

/-! ### The pivotal estimate of mechanism.tex -/

/-- Jensen lower bound `Ent(w^2) ≥ s log(s/b^2)`, `b = E w`, `s = E w^2`. -/
theorem cubeEntropy_sq_ge {n : ℕ} {w : Cube n → ℝ} (hw : ∀ x, 0 ≤ w x) :
    cubeExpect (fun x => w x ^ 2) *
        log (cubeExpect (fun x => w x ^ 2) / cubeExpect w ^ 2) ≤
      cubeEntropy (fun x => w x ^ 2) := by
  set b := cubeExpect w with hb
  set s := cubeExpect (fun x => w x ^ 2) with hs
  have hb0 : 0 ≤ b := cubeExpect_nonneg hw
  rcases hb0.lt_or_eq with hb' | hb'
  · have hvar : 0 ≤ cubeExpect (fun x => (w x - b)^2) :=
      cubeExpect_nonneg (fun x => sq_nonneg _)
    have hexp : cubeExpect (fun x => (w x - b)^2) = s - b^2 := by
      have : (fun x => (w x - b)^2) = fun x => w x ^ 2 + (-2*b) * w x + b^2 := by
        funext x; ring
      rw [this, cubeExpect_add, cubeExpect_add, cubeExpect_mul, cubeExpect_const]
      ring
    have hs0 : 0 < s := by nlinarith
    have hg := gibbs (u := fun x => w x ^ 2) (q := w) (fun x => sq_nonneg _) hw
      (fun x hx => by
        rcases (hw x).lt_or_eq with h | h
        · exact h
        · simp [← h] at hx) hs0 hb'
    have hl : (fun x => w x ^ 2 * log (w x ^ 2)) = fun x => 2 * (w x ^ 2 * log (w x)) := by
      funext x; rw [Real.log_pow]; push_cast; ring
    rw [hl, cubeExpect_mul] at hg
    rw [cubeEntropy_eq_mul_log, hl, cubeExpect_mul, ← hs,
      Real.log_div hs0.ne' (by positivity), Real.log_pow]
    push_cast
    linarith
  · rw [← hb']
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero,
      Real.log_zero, mul_zero]
    have hw0 : ∀ x, w x = 0 := by
      have hsum : ∑ x, w x = 0 := by
        have hwt : GeneralCK.Information.cubeWeight n ≠ 0 := by
          unfold GeneralCK.Information.cubeWeight; positivity
        have : GeneralCK.Information.cubeWeight n * ∑ x, w x = 0 := hb'.symm
        exact (mul_eq_zero.mp this).resolve_left hwt
      intro x
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hw x)).mp hsum x (Finset.mem_univ x)
    have : (fun x => w x ^ 2) = fun _ => (0:ℝ) := by funext x; simp [hw0 x]
    rw [this, cubeEntropy_const]

/-- Pivotal estimate: `E[w Lw] ≥ (s/2) log(s/b^2)` for nonnegative `w`. -/
theorem pivotal_estimate {n : ℕ} {w : Cube n → ℝ} (hw : ∀ x, 0 ≤ w x) :
    cubeExpect (fun x => w x ^ 2) / 2 *
        log (cubeExpect (fun x => w x ^ 2) / cubeExpect w ^ 2) ≤
      cubeExpect (fun x => w x * cubeLaplacian w x) := by
  have h1 := cubeEntropy_sq_ge hw
  have h2 := gross_logSobolev w
  linarith

end MostInformativeBit
