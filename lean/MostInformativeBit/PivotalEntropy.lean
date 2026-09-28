import MostInformativeBit.PivotalGeometry
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Pivotal entropy (mechanism.tex, subsubsection "Pivotal entropy").
`z_i` is defined by the source's actual integral
`z_i = (γ+1)/(γ r^2) ∫_0^{r^2} [1-(t/r^2)^γ] s_i(t) dt`, `s_i(t) = E (T_{√t} q_i)^2`.
We prove its finite Fourier form, `a_i^2 ≤ z_i ≤ a_i`, the Fourier sum for `Z`,
`0 < Z ≤ U ≤ V_0`, and the pivotal entropy inequality
`(γ+1)(U-Z) ≥ (1/2) ∑_i z_i log(z_i/a_i^2)`, by integrating Gross + Jensen.
Coordinates with `a_i = 0` contribute zero on both sides (Lean's `log 0 = 0`
and `z_i = 0`), so all sums run over every coordinate. -/
namespace MostInformativeBit
open scoped BigOperators
open Real intervalIntegral

/-! ### The integral kernel -/

/-- The probability kernel `(γ+1)/(γR) [1-(t/R)^γ]` on `[0,R]`. -/
noncomputable def pivotKernel (γ R t : ℝ) : ℝ := (γ+1)/(γ*R) * (1 - (t/R)^γ)

theorem continuous_pivotKernel {γ R : ℝ} (hγ : 0 < γ) : Continuous (pivotKernel γ R) := by
  unfold pivotKernel
  exact continuous_const.mul (continuous_const.sub
    ((Real.continuous_rpow_const hγ.le).comp (continuous_id.div_const R)))

theorem pivotKernel_nonneg {γ R t : ℝ} (hγ : 0 < γ) (hR : 0 < R) (ht₀ : 0 ≤ t) (ht : t ≤ R) :
    0 ≤ pivotKernel γ R t := by
  unfold pivotKernel
  apply mul_nonneg (by positivity)
  have h1 : t/R ≤ 1 := (div_le_one hR).mpr ht
  have := Real.rpow_le_one (div_nonneg ht₀ hR.le) h1 hγ.le
  linarith

/-- `∫_0^R [1-(t/R)^γ] t^k dt = R^(k+1) γ / ((k+1)(k+1+γ))`. -/
theorem integral_one_sub_rpow_mul_pow {γ R : ℝ} (hγ : 0 < γ) (hR : 0 < R) (k : ℕ) :
    ∫ t in (0:ℝ)..R, (1 - (t/R)^γ) * t^k = R^(k+1) * γ / ((k+1) * (k+1+γ)) := by
  have hcongr : Set.EqOn (fun t : ℝ => (1 - (t/R)^γ) * t^k)
      (fun t => t^k - t^(γ + k) / R^γ) (Set.uIcc 0 R) := by
    intro t ht
    rw [Set.uIcc_of_le hR.le] at ht
    have ht0 : 0 ≤ t := ht.1
    simp only
    rw [Real.div_rpow ht0 hR.le, Real.rpow_add' ht0 (by positivity), Real.rpow_natCast]
    ring
  rw [intervalIntegral.integral_congr hcongr]
  have hi1 : IntervalIntegrable (fun t : ℝ => t^k) MeasureTheory.volume 0 R :=
    (continuous_pow k).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun t : ℝ => t^(γ + k) / R^γ) MeasureTheory.volume 0 R :=
    ((Real.continuous_rpow_const (by positivity)).div_const _).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_div, integral_pow,
    integral_rpow (Or.inl (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]))]
  have h0 : (0:ℝ) ^ (γ + k + 1) = 0 := Real.zero_rpow (by positivity)
  have hRp : R ^ (γ + k + 1) = R^γ * R^(k+1) := by
    rw [show γ + (k:ℝ) + 1 = γ + ((k+1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_add hR, Real.rpow_natCast]
  rw [h0, hRp]
  have hRg : 0 < R^γ := Real.rpow_pos_of_pos hR γ
  simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
    zero_pow, sub_zero]
  field_simp
  ring

/-- Spectral kernel weight `c_k = (γ+1) R^k / ((k+1)(k+1+γ))`. -/
noncomputable def pivotWeight (γ R : ℝ) (k : ℕ) : ℝ := (γ+1) * R^k / ((k+1) * (k+1+γ))

theorem integral_pivotKernel_mul_pow {γ R : ℝ} (hγ : 0 < γ) (hR : 0 < R) (k : ℕ) :
    ∫ t in (0:ℝ)..R, pivotKernel γ R t * t^k = pivotWeight γ R k := by
  unfold pivotKernel pivotWeight
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul, integral_one_sub_rpow_mul_pow hγ hR]
  field_simp
  ring

theorem pivotWeight_zero (γ R : ℝ) (hγ : 0 < γ) : pivotWeight γ R 0 = 1 := by
  unfold pivotWeight
  simp only [pow_zero, Nat.cast_zero, zero_add, mul_one, one_mul]
  rw [add_comm, div_self (by positivity)]

theorem integral_pivotKernel {γ R : ℝ} (hγ : 0 < γ) (hR : 0 < R) :
    ∫ t in (0:ℝ)..R, pivotKernel γ R t = 1 := by
  have h := integral_pivotKernel_mul_pow hγ hR 0
  simp only [pow_zero, mul_one] at h
  rw [h, pivotWeight_zero _ _ hγ]

/-- Integral of the kernel against a finite spectral polynomial. -/
theorem integral_pivotKernel_spectral {n : ℕ} {γ R : ℝ} (hγ : 0 < γ) (hR : 0 < R)
    (c : Finset (Fin n) → ℝ) :
    ∫ t in (0:ℝ)..R, pivotKernel γ R t * ∑ S : Finset (Fin n), c S * t^S.card =
      ∑ S : Finset (Fin n), c S * pivotWeight γ R S.card := by
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro S _
    rw [show (fun t => pivotKernel γ R t * (c S * t^S.card)) =
        fun t => c S * (pivotKernel γ R t * t^S.card) by ext t; ring,
      intervalIntegral.integral_const_mul, integral_pivotKernel_mul_pow hγ hR]
  · intro S _
    exact ((continuous_pivotKernel hγ).mul (continuous_const.mul (continuous_pow _)))
      |>.intervalIntegrable _ _

theorem continuous_spectral {n : ℕ} (c : Finset (Fin n) → ℝ) :
    Continuous (fun t : ℝ => ∑ S : Finset (Fin n), c S * t^S.card) := by
  fun_prop

theorem pivotWeight_nonneg {γ R : ℝ} (hγ : 0 < γ) (hR : 0 ≤ R) (k : ℕ) :
    0 ≤ pivotWeight γ R k := by
  unfold pivotWeight; positivity

theorem pivotWeight_le_one {γ R : ℝ} (hγ : 0 < γ) (hR₀ : 0 ≤ R) (hR₁ : R ≤ 1) (k : ℕ) :
    pivotWeight γ R k ≤ 1 := by
  unfold pivotWeight
  rw [div_le_one (by positivity)]
  have hk : R^k ≤ 1 := pow_le_one₀ hR₀ hR₁
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

/-! ### Smoothed pivotal indicators -/

/-- `s_i(t) = E (T_{√t} q_i)^2`, the source's pivotal energy. -/
noncomputable def pivotalEnergy {n : ℕ} (i : Fin n) (f : Cube n → Bool) (t : ℝ) : ℝ :=
  cubeExpect (fun x => noise (√t) (pivotal i f) x ^ 2)

/-- The source's pivotal average, defined by the actual integral. -/
noncomputable def pivotalAverage {n : ℕ} (γ r : ℝ) (i : Fin n) (f : Cube n → Bool) : ℝ :=
  (γ+1)/(γ*r^2) * ∫ t in (0:ℝ)..r^2, (1 - (t/r^2)^γ) * pivotalEnergy i f t

noncomputable def pivotalTotal {n : ℕ} (γ r : ℝ) (f : Cube n → Bool) : ℝ :=
  ∑ i, pivotalAverage γ r i f

/-- `U = Var(u)/r^2`, `u = T_r f`. -/
noncomputable def noisyVarRatio {n : ℕ} (r : ℝ) (f : Cube n → Bool) : ℝ :=
  (cubeExpect (fun x => noise r (signField f) x ^ 2) -
    cubeExpect (noise r (signField f)) ^ 2) / r^2

/-- `V_0 = 1 - m^2`. -/
noncomputable def meanDefect {n : ℕ} (f : Cube n → Bool) : ℝ :=
  1 - cubeExpect (signField f) ^ 2

theorem pivotalEnergy_eq {n : ℕ} (i : Fin n) (f : Cube n → Bool) {t : ℝ} (ht : 0 ≤ t) :
    pivotalEnergy i f t =
      ∑ S : Finset (Fin n), fourierCoeff (pivotal i f) S ^ 2 * t^S.card := by
  rw [pivotalEnergy, noise_energy]
  apply Finset.sum_congr rfl
  intro S _
  rw [pow_mul, Real.sq_sqrt ht]; ring

theorem pivotalDirichlet_eq {n : ℕ} (i : Fin n) (f : Cube n → Bool) {t : ℝ} (ht : 0 ≤ t) :
    cubeExpect (fun x => noise (√t) (pivotal i f) x *
        cubeLaplacian (noise (√t) (pivotal i f)) x) =
      ∑ S : Finset (Fin n), (S.card * fourierCoeff (pivotal i f) S ^ 2) * t^S.card := by
  rw [noise_laplacian_energy]
  apply Finset.sum_congr rfl
  intro S _
  rw [pow_mul, Real.sq_sqrt ht]; ring

theorem pivotalAverage_eq_kernel {n : ℕ} {γ r : ℝ} (hγ : 0 < γ) (hr : 0 < r)
    (i : Fin n) (f : Cube n → Bool) :
    pivotalAverage γ r i f = ∫ t in (0:ℝ)..r^2, pivotKernel γ (r^2) t *
      ∑ S : Finset (Fin n), fourierCoeff (pivotal i f) S ^ 2 * t^S.card := by
  unfold pivotalAverage
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (by positivity)] at ht
  simp only [pivotKernel, pivotalEnergy_eq i f ht.1]
  ring

/-- Finite Fourier form of the pivotal average. -/
theorem pivotalAverage_eq_sum {n : ℕ} {γ r : ℝ} (hγ : 0 < γ) (hr : 0 < r)
    (i : Fin n) (f : Cube n → Bool) :
    pivotalAverage γ r i f = ∑ S : Finset (Fin n),
      fourierCoeff (pivotal i f) S ^ 2 * pivotWeight γ (r^2) S.card := by
  rw [pivotalAverage_eq_kernel hγ hr, integral_pivotKernel_spectral hγ (by positivity)]

/-- `a_i^2 ≤ z_i ≤ a_i`. -/
theorem pivotalAverage_bounds {n : ℕ} {γ r : ℝ} (hγ : 0 < γ) (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    {f : Cube n → Bool} (hf : Monotone f) (i : Fin n) :
    pivotalMean i f ^ 2 ≤ pivotalAverage γ r i f ∧
      pivotalAverage γ r i f ≤ pivotalMean i f := by
  rw [pivotalAverage_eq_sum hγ hr₀]
  have hR0 : 0 ≤ r^2 := sq_nonneg r
  have hR1 : r^2 ≤ 1 := by nlinarith
  constructor
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ∅)]
    have hrest : 0 ≤ ∑ S ∈ Finset.univ.erase ∅,
        fourierCoeff (pivotal i f) S ^ 2 * pivotWeight γ (r^2) S.card :=
      Finset.sum_nonneg (fun S _ => mul_nonneg (sq_nonneg _) (pivotWeight_nonneg hγ hR0 _))
    have h0 : fourierCoeff (pivotal i f) ∅ = pivotalMean i f := by
      rw [fourierCoeff_empty, cubeExpect_pivotal]
    rw [h0, Finset.card_empty, pivotWeight_zero _ _ hγ, mul_one]
    linarith
  · rw [← sum_sq_fourierCoeff_pivotal hf i]
    apply Finset.sum_le_sum
    intro S _
    exact mul_le_of_le_one_right (sq_nonneg _) (pivotWeight_le_one hγ hR0 hR1 _)

theorem pivotalAverage_eq_zero_of_mean {n : ℕ} {γ r : ℝ} (hγ : 0 < γ) (hr₀ : 0 < r)
    (hr₁ : r ≤ 1) {f : Cube n → Bool} (hf : Monotone f) (i : Fin n)
    (h : pivotalMean i f = 0) : pivotalAverage γ r i f = 0 := by
  have hb := pivotalAverage_bounds hγ hr₀ hr₁ hf i
  rw [h] at hb
  simp at hb
  linarith [hb.1, hb.2]

/-! ### Fourier forms of `Z`, `U`, `V_0` -/

theorem pivotalTotal_eq {n : ℕ} {γ r : ℝ} (hγ : 0 < γ) (hr : 0 < r) (f : Cube n → Bool) :
    pivotalTotal γ r f = (γ+1) * ∑ T : Finset (Fin n),
      (if T = ∅ then 0 else r^(2*(T.card-1)) / (γ+T.card) * fourierCoeff (signField f) T ^ 2) := by
  unfold pivotalTotal
  simp_rw [pivotalAverage_eq_sum hγ hr, fourierCoeff_pivotal]
  have h : ∀ i : Fin n, (∑ S : Finset (Fin n),
      (if i ∈ S then 0 else fourierCoeff (signField f) (insert i S)) ^ 2 *
        pivotWeight γ (r^2) S.card) =
      ∑ S : Finset (Fin n), if i ∈ S then 0 else
        fourierCoeff (signField f) (insert i S) ^ 2 * pivotWeight γ (r^2) ((insert i S).card - 1) := by
    intro i
    apply Finset.sum_congr rfl
    intro S _
    split_ifs with hS
    · simp
    · rw [Finset.card_insert_of_notMem hS, Nat.add_sub_cancel]
  simp_rw [h]
  rw [sum_coord_insert (fun T => fourierCoeff (signField f) T ^ 2 *
    pivotWeight γ (r^2) (T.card - 1)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  split_ifs with hT
  · simp [hT]
  · have hc : 1 ≤ T.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hT)
    unfold pivotWeight
    rw [Nat.cast_sub hc, Nat.cast_one, sub_add_cancel, ← pow_mul]
    have hk : (0:ℝ) < T.card := by exact_mod_cast hc
    field_simp
    ring

theorem sum_ite_empty {n : ℕ} (g : Finset (Fin n) → ℝ) :
    (∑ T : Finset (Fin n), if T = ∅ then 0 else g T) = (∑ T : Finset (Fin n), g T) - g ∅ := by
  rw [← Finset.add_sum_erase _ g (Finset.mem_univ ∅),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ (∅ : Finset (Fin n))),
    Finset.sum_congr rfl (fun T hT => if_neg (Finset.ne_of_mem_erase hT))]
  simp

theorem noisyVariance_eq {n : ℕ} (r : ℝ) (f : Cube n → Bool) :
    cubeExpect (fun x => noise r (signField f) x ^ 2) -
        cubeExpect (noise r (signField f)) ^ 2 =
      ∑ T : Finset (Fin n),
        (if T = ∅ then 0 else r^(2*T.card) * fourierCoeff (signField f) T ^ 2) := by
  rw [noise_energy, cubeExpect_noise, sum_ite_empty]
  simp

theorem noisyVarRatio_eq {n : ℕ} {r : ℝ} (hr : 0 < r) (f : Cube n → Bool) :
    noisyVarRatio r f = ∑ T : Finset (Fin n),
      (if T = ∅ then 0 else r^(2*(T.card-1)) * fourierCoeff (signField f) T ^ 2) := by
  unfold noisyVarRatio
  rw [noisyVariance_eq, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro T _
  split_ifs with hT
  · simp
  · have hc : 1 ≤ T.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hT)
    rw [show 2*T.card = 2*(T.card-1) + 2 by omega, pow_add]
    field_simp

theorem meanDefect_eq {n : ℕ} (f : Cube n → Bool) :
    meanDefect f = ∑ T : Finset (Fin n),
      (if T = ∅ then 0 else fourierCoeff (signField f) T ^ 2) := by
  unfold meanDefect
  rw [← signField_parseval f, sum_ite_empty]
  simp

/-- `Z ≤ U ≤ V_0`. -/
theorem pivotalTotal_le_noisyVarRatio {n : ℕ} {γ r : ℝ} (hγ : 0 < γ) (hr : 0 < r)
    (f : Cube n → Bool) : pivotalTotal γ r f ≤ noisyVarRatio r f := by
  rw [pivotalTotal_eq hγ hr, noisyVarRatio_eq hr, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro T _
  split_ifs with hT
  · simp
  · have hc : (1:ℝ) ≤ T.card := by
      exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hT)
    have hq : (γ+1) / (γ + T.card) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have hnn : 0 ≤ r^(2*(T.card-1)) * fourierCoeff (signField f) T ^ 2 := by positivity
    calc (γ+1) * (r^(2*(T.card-1)) / (γ+T.card) * fourierCoeff (signField f) T ^ 2)
        = (γ+1) / (γ + T.card) * (r^(2*(T.card-1)) * fourierCoeff (signField f) T ^ 2) := by
          ring
      _ ≤ 1 * (r^(2*(T.card-1)) * fourierCoeff (signField f) T ^ 2) :=
          mul_le_mul_of_nonneg_right hq hnn
      _ = _ := one_mul _

theorem noisyVarRatio_le_meanDefect {n : ℕ} {r : ℝ} (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (f : Cube n → Bool) : noisyVarRatio r f ≤ meanDefect f := by
  rw [noisyVarRatio_eq hr₀, meanDefect_eq]
  apply Finset.sum_le_sum
  intro T _
  split_ifs
  · rfl
  · exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ hr₀.le hr₁)

/-- `Z > 0` for nonconstant `f` (monotonicity is not needed). -/
theorem pivotalTotal_pos {n : ℕ} {γ r : ℝ} (hγ : 0 < γ) (hr : 0 < r)
    {f : Cube n → Bool} (hf : ∃ x y, f x ≠ f y) : 0 < pivotalTotal γ r f := by
  have hV : 0 < meanDefect f := by
    obtain ⟨x, y, hxy⟩ := hf
    set m := cubeExpect (signField f)
    have hvar : meanDefect f = cubeExpect (fun z => (signField f z - m)^2) := by
      have : (fun z => (signField f z - m)^2) =
          fun z => signField f z ^ 2 + (-2*m) * signField f z + m^2 := by funext z; ring
      rw [this, cubeExpect_add, cubeExpect_add, cubeExpect_mul, cubeExpect_const]
      have hs : (fun z => signField f z ^ 2) = fun _ => (1:ℝ) := by
        funext z; exact cubeSign_sq (f z)
      rw [hs, cubeExpect_const, meanDefect]
      ring
    rw [hvar]
    have hne : signField f x ≠ signField f y := by
      unfold signField
      cases hx : f x <;> cases hy : f y <;> simp_all [cubeSign] <;> norm_num
    have hpos : ∃ z, 0 < (signField f z - m)^2 := by
      by_cases hx : signField f x = m
      · exact ⟨y, by have : signField f y - m ≠ 0 := fun h => hne (by linarith); positivity⟩
      · exact ⟨x, by have : signField f x - m ≠ 0 := sub_ne_zero.mpr hx; positivity⟩
    obtain ⟨z, hz⟩ := hpos
    apply mul_pos (by unfold GeneralCK.Information.cubeWeight; positivity)
    exact Finset.sum_pos' (fun w _ => sq_nonneg _) ⟨z, Finset.mem_univ z, hz⟩
  rw [meanDefect_eq] at hV
  rw [pivotalTotal_eq hγ hr]
  apply mul_pos (by linarith)
  obtain ⟨T, _, hT⟩ := Finset.exists_lt_of_sum_lt (by simpa using hV :
    ∑ T : Finset (Fin n), (0:ℝ) <
      ∑ T : Finset (Fin n), if T = ∅ then 0 else fourierCoeff (signField f) T ^ 2)
  apply Finset.sum_pos' (fun S _ => by split_ifs <;> positivity) ⟨T, Finset.mem_univ T, ?_⟩
  split_ifs with h
  · simp [h] at hT
  · rw [if_neg h] at hT
    positivity

/-! ### Pivotal entropy inequality -/

/-- Tangent-line (Jensen) inequality for `s ↦ s log(s/a^2)`. -/
theorem slog_tangent {s z c : ℝ} (hs : 0 < s) (hz : 0 < z) (hc : 0 < c) :
    z * log (z/c) + (log (z/c) + 1) * (s - z) ≤ s * log (s/c) := by
  have hl := Real.log_le_sub_one_of_pos (div_pos hz hs)
  rw [Real.log_div hz.ne' hs.ne'] at hl
  rw [Real.log_div hz.ne' hc.ne', Real.log_div hs.ne' hc.ne']
  have := mul_le_mul_of_nonneg_left hl hs.le
  have he : s * (z/s - 1) = z - s := by field_simp
  nlinarith

/-- Per-coordinate Dirichlet average: `Y_i = ∑_S |S| c_{|S|} q̂_i(S)^2`. -/
noncomputable def pivotalDirichletAverage {n : ℕ} (γ r : ℝ) (i : Fin n) (f : Cube n → Bool) :
    ℝ :=
  ∑ S : Finset (Fin n), (S.card * fourierCoeff (pivotal i f) S ^ 2) * pivotWeight γ (r^2) S.card

/-- Gross + Jensen, averaged with the kernel defining `z_i`. -/
theorem pivotal_entropy_coordinate {n : ℕ} {γ r : ℝ} (hγ : 0 < γ) (hr₀ : 0 < r)
    (hr₁ : r ≤ 1) {f : Cube n → Bool} (hf : Monotone f) (i : Fin n) :
    pivotalAverage γ r i f / 2 * log (pivotalAverage γ r i f / pivotalMean i f ^ 2) ≤
      pivotalDirichletAverage γ r i f := by
  set a := pivotalMean i f with ha
  set z := pivotalAverage γ r i f with hz
  have hR : 0 < r^2 := by positivity
  have hY0 : 0 ≤ pivotalDirichletAverage γ r i f :=
    Finset.sum_nonneg (fun S _ => mul_nonneg (by positivity) (pivotWeight_nonneg hγ hR.le _))
  rcases (pivotalMean_nonneg hf i).lt_or_eq with ha0 | ha0
  swap
  · have h0 : a = 0 := by rw [ha]; exact ha0.symm
    rw [h0]; simpa using hY0
  have hzb := pivotalAverage_bounds hγ hr₀ hr₁ hf i
  have hz0 : 0 < z := lt_of_lt_of_le (by positivity) hzb.1
  set c : Finset (Fin n) → ℝ := fun S => fourierCoeff (pivotal i f) S ^ 2 with hc
  set e : Finset (Fin n) → ℝ := fun S => S.card * fourierCoeff (pivotal i f) S ^ 2 with he
  set sp : ℝ → ℝ := fun t => ∑ S : Finset (Fin n), c S * t^S.card with hsp
  set ep : ℝ → ℝ := fun t => ∑ S : Finset (Fin n), e S * t^S.card with hep
  -- pointwise Gross + Jensen on [0, r^2]
  have hpt : ∀ t ∈ Set.Icc (0:ℝ) (r^2),
      pivotKernel γ (r^2) t * ((z * log (z/a^2) - (log (z/a^2) + 1) * z) / 2 +
        (log (z/a^2) + 1) / 2 * sp t) ≤ pivotKernel γ (r^2) t * ep t := by
    intro t ht
    apply mul_le_mul_of_nonneg_left _ (pivotKernel_nonneg hγ hR ht.1 ht.2)
    have hst : √t ≤ 1 := by
      rw [Real.sqrt_le_one]; nlinarith [ht.2]
    have hw : ∀ x, 0 ≤ noise (√t) (pivotal i f) x := by
      intro x
      simpa using noise_mono (r := √t) (by linarith [Real.sqrt_nonneg t]) hst
        (v := fun _ => (0:ℝ)) (fun y => pivotal_nonneg hf i y) x
    have hpiv := pivotal_estimate hw
    rw [cubeExpect_noise, cubeExpect_pivotal, ← pivotalEnergy,
      pivotalEnergy_eq i f ht.1, pivotalDirichlet_eq i f ht.1] at hpiv
    have hspa : a^2 ≤ sp t := by
      simp only [hsp, hc]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ∅)]
      have : 0 ≤ ∑ S ∈ Finset.univ.erase ∅, fourierCoeff (pivotal i f) S ^ 2 * t^S.card :=
        Finset.sum_nonneg (fun S _ => mul_nonneg (sq_nonneg _) (pow_nonneg ht.1 _))
      rw [fourierCoeff_empty, cubeExpect_pivotal, Finset.card_empty, pow_zero, mul_one]
      linarith
    have htan := slog_tangent (lt_of_lt_of_le (by positivity) hspa) hz0 (by positivity : 0 < a^2)
    simp only [hep, he, hsp, hc] at hpiv htan ⊢
    nlinarith
  have hint : (∫ t in (0:ℝ)..r^2, pivotKernel γ (r^2) t *
      ((z * log (z/a^2) - (log (z/a^2) + 1) * z) / 2 + (log (z/a^2) + 1) / 2 * sp t)) ≤
      ∫ t in (0:ℝ)..r^2, pivotKernel γ (r^2) t * ep t := intervalIntegral.integral_mono_on hR.le
    (Continuous.intervalIntegrable (μ := MeasureTheory.volume)
      ((continuous_pivotKernel hγ).mul (continuous_const.add
        (continuous_const.mul (continuous_spectral c)))) 0 (r^2))
    (Continuous.intervalIntegrable (μ := MeasureTheory.volume)
      ((continuous_pivotKernel hγ).mul (continuous_spectral e)) 0 (r^2)) hpt
  have hL : ∫ t in (0:ℝ)..r^2, pivotKernel γ (r^2) t *
      ((z * log (z/a^2) - (log (z/a^2) + 1) * z) / 2 + (log (z/a^2) + 1) / 2 * sp t) =
      (z * log (z/a^2) - (log (z/a^2) + 1) * z) / 2 +
        (log (z/a^2) + 1) / 2 * z := by
    have hz' : z = ∫ t in (0:ℝ)..r^2, pivotKernel γ (r^2) t * sp t :=
      pivotalAverage_eq_kernel hγ hr₀ i f
    simp_rw [mul_add]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_mul_const,
      integral_pivotKernel hγ hR]
    · rw [show (fun t => pivotKernel γ (r^2) t * ((log (z/a^2) + 1) / 2 * sp t)) =
          fun t => (log (z/a^2) + 1) / 2 * (pivotKernel γ (r^2) t * sp t) by ext t; ring,
        intervalIntegral.integral_const_mul, ← hz']
      ring
    · exact ((continuous_pivotKernel hγ).mul continuous_const).intervalIntegrable _ _
    · exact ((continuous_pivotKernel hγ).mul
        (continuous_const.mul (continuous_spectral c))).intervalIntegrable _ _
  have hR' : ∫ t in (0:ℝ)..r^2, pivotKernel γ (r^2) t * ep t =
      pivotalDirichletAverage γ r i f :=
    integral_pivotKernel_spectral hγ hR e
  rw [hL, hR'] at hint
  linarith

/-- `(γ+1)(U - Z) = ∑_i Y_i`, the Fourier-degree expansion. -/
theorem sum_pivotalDirichletAverage {n : ℕ} {γ r : ℝ} (hγ : 0 < γ) (hr : 0 < r)
    (f : Cube n → Bool) :
    (∑ i, pivotalDirichletAverage γ r i f) =
      (γ+1) * (noisyVarRatio r f - pivotalTotal γ r f) := by
  unfold pivotalDirichletAverage
  simp_rw [fourierCoeff_pivotal]
  have h : ∀ i : Fin n, (∑ S : Finset (Fin n),
      (S.card * (if i ∈ S then 0 else fourierCoeff (signField f) (insert i S)) ^ 2) *
        pivotWeight γ (r^2) S.card) =
      ∑ S : Finset (Fin n), if i ∈ S then 0 else
        ((insert i S).card - 1 : ℕ) * fourierCoeff (signField f) (insert i S) ^ 2 *
          pivotWeight γ (r^2) ((insert i S).card - 1) := by
    intro i
    apply Finset.sum_congr rfl
    intro S _
    split_ifs with hS
    · simp
    · rw [Finset.card_insert_of_notMem hS, Nat.add_sub_cancel]
  simp_rw [h]
  rw [sum_coord_insert (fun T => ((T.card - 1 : ℕ) : ℝ) * fourierCoeff (signField f) T ^ 2 *
    pivotWeight γ (r^2) (T.card - 1)), pivotalTotal_eq hγ hr, noisyVarRatio_eq hr,
    Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  split_ifs with hT
  · simp [hT]
  · have hc : 1 ≤ T.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hT)
    unfold pivotWeight
    rw [Nat.cast_sub hc, Nat.cast_one, sub_add_cancel, ← pow_mul]
    have hk : (0:ℝ) < T.card := by exact_mod_cast hc
    field_simp
    ring

/-- The source's pivotal entropy inequality (eq:pivotal-entropy):
`(γ+1)(U-Z) ≥ (1/2) E_piv`, `E_piv = ∑_i z_i log(z_i/a_i^2)`. -/
theorem pivotal_entropy {n : ℕ} {γ r : ℝ} (hγ : 0 < γ) (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    {f : Cube n → Bool} (hf : Monotone f) :
    (∑ i, pivotalAverage γ r i f * log (pivotalAverage γ r i f / pivotalMean i f ^ 2)) / 2 ≤
      (γ+1) * (noisyVarRatio r f - pivotalTotal γ r f) := by
  rw [← sum_pivotalDirichletAverage hγ hr₀, Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  have := pivotal_entropy_coordinate hγ hr₀ hr₁ hf i
  linarith

end MostInformativeBit
