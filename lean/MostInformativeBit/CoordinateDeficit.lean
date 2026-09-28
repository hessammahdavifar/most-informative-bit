import MostInformativeBit.PivotalEntropy

/-! Coordinate deficit bounds (mechanism.tex, Lemma "Coordinate deficit
bounds", `lem:deficit`). For monotone Boolean `f`, `u = T_r f`, `γ > 0`,
`0 < r ≤ 1`, real degree `D ≥ 2`:
`D_i ≤ min {K r^2 a_i^2, d_2/2 a_i + (d_1 - d_2/2) a_i^2}` and
`∑_{S≠∅} ω(|S|) û(S)^2 ≥ ω(D) Var(u) - ∑_i D(a_i)`.
The first branch integrates the Gross estimate along `w_t = T_{√t} p_i`, with
the source's integral representation of `D_i` proved exactly. -/
namespace MostInformativeBit
open scoped BigOperators
open Real

/-- `ω(s) = γ s / (γ + s)`. -/
noncomputable def degWeight (γ s : ℝ) : ℝ := γ * s / (γ + s)

/-- `K = γ^2 e^{2D-3} / (2 (γ+D)(γ+1))`. -/
noncomputable def lsiConst (γ D : ℝ) : ℝ :=
  γ^2 * exp (2*D - 3) / (2 * (γ + D) * (γ + 1))

/-- `d_j = [ω(D) - ω(j)] r^{2j}`. -/
noncomputable def deficitCoeff (γ D r : ℝ) (j : ℕ) : ℝ :=
  (degWeight γ D - degWeight γ j) * r^(2*j)

/-- The source's coordinate deficit `D_i = ∑_{S ∋ i} (ω(D)-ω(|S|))/|S| û(S)^2`. -/
noncomputable def coordDeficit {n : ℕ} (γ D r : ℝ) (f : Cube n → Bool) (i : Fin n) : ℝ :=
  ∑ S : Finset (Fin n), if i ∈ S then
    (degWeight γ D - degWeight γ S.card) / S.card *
      fourierCoeff (noise r (signField f)) S ^ 2 else 0

/-- `D(a) = min {K r^2 a^2, d_2/2 a + (d_1 - d_2/2) a^2}`. -/
noncomputable def deficitBound (γ D r a : ℝ) : ℝ :=
  min (lsiConst γ D * r^2 * a^2)
    (deficitCoeff γ D r 2 / 2 * a + (deficitCoeff γ D r 1 - deficitCoeff γ D r 2 / 2) * a^2)

theorem degWeight_mono {γ s s' : ℝ} (hγ : 0 < γ) (hs : 0 ≤ s) (hss : s ≤ s') :
    degWeight γ s ≤ degWeight γ s' := by
  unfold degWeight
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_nonneg (mul_nonneg hγ.le hγ.le) (sub_nonneg.mpr hss)]

/-! ### Scalar minimization -/

/-- `(D-1)s - (s/2) log(s/b^2) ≤ e^{2D-3} b^2 / 2`, the minimization over `s`. -/
theorem quad_log_bound {s b D : ℝ} (hb : 0 < b) (hs : 0 < s) :
    (D-1)*s - s/2 * log (s/b^2) ≤ exp (2*D-3) * b^2 / 2 := by
  set c := b^2 * exp (2*D-3) with hc
  have hc0 : 0 < c := by positivity
  set x := s / c with hx
  have hx0 : 0 < x := div_pos hs hc0
  have hsx : s = c * x := by rw [hx]; field_simp
  have hlog : log (s/b^2) = log x + (2*D-3) := by
    rw [show s/b^2 = x * exp (2*D-3) by rw [hsx, hc]; field_simp, Real.log_mul hx0.ne'
      (Real.exp_pos _).ne', Real.log_exp]
  rw [hlog]
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hx0)
  rw [Real.log_inv] at hl
  have hxl : x - 1 ≤ x * log x := by
    have := mul_le_mul_of_nonneg_left hl hx0.le
    have he : x * (x⁻¹ - 1) = 1 - x := by field_simp
    nlinarith
  have : s/2 - s/2 * log x ≤ c/2 := by
    rw [hsx]; nlinarith
  rw [hc] at this
  nlinarith

/-! ### Section derivative of the noisy function -/

theorem fourierCoeff_noiseSection {n : ℕ} (r : ℝ) (f : Cube n → Bool) (i : Fin n)
    (S : Finset (Fin n)) :
    fourierCoeff (sectionDiff i (noise r (signField f))) S =
      if i ∈ S then 0 else fourierCoeff (noise r (signField f)) (insert i S) :=
  fourierCoeff_sectionDiff i _ S

theorem noiseSection_nonneg {n : ℕ} {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1)
    {f : Cube n → Bool} (hf : Monotone f) (i : Fin n) (x : Cube n) :
    0 ≤ sectionDiff i (noise r (signField f)) x := by
  rw [sectionDiff_noise_signField]
  apply mul_nonneg hr₀
  simpa using noise_mono (r := r) (by linarith) hr₁ (v := fun _ => (0:ℝ))
    (fun y => pivotal_nonneg hf i y) x

theorem cubeExpect_noiseSection {n : ℕ} (r : ℝ) (f : Cube n → Bool) (i : Fin n) :
    cubeExpect (sectionDiff i (noise r (signField f))) = r * pivotalMean i f := by
  rw [sectionDiff_noise_signField, cubeExpect_mul, cubeExpect_noise, cubeExpect_pivotal]

/-- `D_i` in terms of the coefficients of `p_i`. -/
theorem coordDeficit_eq_section {n : ℕ} (γ D r : ℝ) (f : Cube n → Bool) (i : Fin n) :
    coordDeficit γ D r f i = ∑ S : Finset (Fin n),
      (degWeight γ D - degWeight γ (S.card + 1)) / (S.card + 1) *
        fourierCoeff (sectionDiff i (noise r (signField f))) S ^ 2 := by
  unfold coordDeficit
  rw [← sum_insert_reindex]
  apply Finset.sum_congr rfl
  intro S _
  rw [fourierCoeff_noiseSection]
  split_ifs with hS
  · simp
  · rw [Finset.card_insert_of_notMem hS]; push_cast; ring

/-! ### First branch: integrated Gross estimate -/

/-- The source's integrand `E[w_t (D-1-L_{-i}) w_t]`, `w_t = T_{√t} p_i`. -/
noncomputable def deficitIntegrand {n : ℕ} (D r : ℝ) (f : Cube n → Bool) (i : Fin n)
    (t : ℝ) : ℝ :=
  let w := noise (√t) (sectionDiff i (noise r (signField f)))
  (D-1) * cubeExpect (fun x => w x ^ 2) - cubeExpect (fun x => w x * cubeLaplacian w x)

theorem deficitIntegrand_eq {n : ℕ} (D r : ℝ) (f : Cube n → Bool) (i : Fin n) {t : ℝ}
    (ht : 0 ≤ t) :
    deficitIntegrand D r f i t = ∑ S : Finset (Fin n),
      ((D - 1 - S.card) * fourierCoeff (sectionDiff i (noise r (signField f))) S ^ 2) *
        t^S.card := by
  unfold deficitIntegrand
  simp only
  rw [noise_energy, noise_laplacian_energy, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S _
  rw [pow_mul, Real.sq_sqrt ht]; ring

theorem integral_one_sub_rpow_spectral {n : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (c : Finset (Fin n) → ℝ) :
    ∫ t in (0:ℝ)..1, (1 - t^γ) * ∑ S : Finset (Fin n), c S * t^S.card =
      ∑ S : Finset (Fin n), c S * (γ / ((S.card + 1) * (S.card + 1 + γ))) := by
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro S _
    have h := integral_one_sub_rpow_mul_pow hγ one_pos S.card
    simp only [div_one, one_pow, one_mul] at h
    rw [show (fun t : ℝ => (1 - t^γ) * (c S * t^S.card)) =
        fun t => c S * ((1 - t^γ) * t^S.card) by ext t; ring,
      intervalIntegral.integral_const_mul, h]
  · intro S _
    exact Continuous.intervalIntegrable (μ := MeasureTheory.volume)
      ((continuous_const.sub (Real.continuous_rpow_const hγ.le)).mul
        (continuous_const.mul (continuous_pow _))) 0 1

/-- The source's integral representation
`D_i = γ/(γ+D) ∫_0^1 (1-t^γ) E[w_t (D-1-L_{-i}) w_t] dt`. -/
theorem coordDeficit_integral {n : ℕ} {γ D r : ℝ} (hγ : 0 < γ) (hD : 0 < γ + D)
    (f : Cube n → Bool) (i : Fin n) :
    coordDeficit γ D r f i =
      γ / (γ + D) * ∫ t in (0:ℝ)..1, (1 - t^γ) * deficitIntegrand D r f i t := by
  have hcongr : Set.EqOn (fun t => (1 - t^γ) * deficitIntegrand D r f i t)
      (fun t => (1 - t^γ) * ∑ S : Finset (Fin n),
        ((D - 1 - S.card) * fourierCoeff (sectionDiff i (noise r (signField f))) S ^ 2) *
          t^S.card) (Set.uIcc 0 1) := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    simp only [deficitIntegrand_eq D r f i ht.1]
  rw [intervalIntegral.integral_congr hcongr, integral_one_sub_rpow_spectral hγ,
    coordDeficit_eq_section, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  unfold degWeight
  have h1 : (0:ℝ) < S.card + 1 := by positivity
  have h2 : (0:ℝ) < γ + (S.card + 1) := by positivity
  field_simp
  ring

theorem deficitIntegrand_le {n : ℕ} {D r : ℝ} (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    {f : Cube n → Bool} (hf : Monotone f) (i : Fin n) (ha : 0 < pivotalMean i f)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    deficitIntegrand D r f i t ≤ exp (2*D-3) * (r * pivotalMean i f)^2 / 2 := by
  set p := sectionDiff i (noise r (signField f)) with hp
  set w := noise (√t) p with hw
  have hst : √t ≤ 1 := Real.sqrt_le_one.mpr ht₁
  have hw0 : ∀ x, 0 ≤ w x := by
    intro x
    simpa using noise_mono (r := √t) (by linarith [Real.sqrt_nonneg t]) hst
      (v := fun _ => (0:ℝ)) (fun y => noiseSection_nonneg hr₀.le hr₁ hf i y) x
  have hb : cubeExpect w = r * pivotalMean i f := by
    rw [hw, cubeExpect_noise, hp, cubeExpect_noiseSection]
  have hb0 : 0 < r * pivotalMean i f := mul_pos hr₀ ha
  have hpiv := pivotal_estimate hw0
  rw [hb] at hpiv
  set s := cubeExpect (fun x => w x ^ 2) with hs
  have hvar : 0 ≤ cubeExpect (fun x => (w x - r * pivotalMean i f)^2) :=
    cubeExpect_nonneg (fun x => sq_nonneg _)
  have hexp : cubeExpect (fun x => (w x - r * pivotalMean i f)^2) =
      s - (r * pivotalMean i f)^2 := by
    have : (fun x => (w x - r * pivotalMean i f)^2) =
        fun x => w x ^ 2 + (-2 * (r * pivotalMean i f)) * w x + (r * pivotalMean i f)^2 := by
      funext x; ring
    rw [this, cubeExpect_add, cubeExpect_add, cubeExpect_mul, cubeExpect_const, hb]
    ring
  have hs0 : 0 < s := by nlinarith
  have hq := quad_log_bound (D := D) hb0 hs0
  have hdef : deficitIntegrand D r f i t =
      (D-1) * s - cubeExpect (fun x => w x * cubeLaplacian w x) := rfl
  rw [hdef]
  linarith

theorem integral_one_sub_rpow {γ : ℝ} (hγ : 0 < γ) :
    ∫ t in (0:ℝ)..1, (1 - t^γ) = γ / (γ + 1) := by
  have h := integral_one_sub_rpow_mul_pow hγ one_pos 0
  simp only [div_one, pow_zero, mul_one, one_pow, Nat.cast_zero, zero_add, one_mul] at h
  rw [h]; ring

/-- First branch: `D_i ≤ K r^2 a_i^2`. -/
theorem coordDeficit_le_lsi {n : ℕ} {γ D r : ℝ} (hγ : 0 < γ) (hD : 2 ≤ D) (hr₀ : 0 < r)
    (hr₁ : r ≤ 1) {f : Cube n → Bool} (hf : Monotone f) (i : Fin n) :
    coordDeficit γ D r f i ≤ lsiConst γ D * r^2 * pivotalMean i f ^ 2 := by
  have hγD : 0 < γ + D := by linarith
  rcases (pivotalMean_nonneg hf i).lt_or_eq with ha | ha
  · rw [coordDeficit_integral hγ hγD]
    set B := exp (2*D-3) * (r * pivotalMean i f)^2 / 2 with hB
    have hmono : (∫ t in (0:ℝ)..1, (1 - t^γ) * deficitIntegrand D r f i t) ≤
        ∫ t in (0:ℝ)..1, (1 - t^γ) * B := by
      apply intervalIntegral.integral_mono_on zero_le_one
      · have hc : ContinuousOn (fun t => (1 - t^γ) * deficitIntegrand D r f i t)
            (Set.uIcc 0 1) := by
          have hcon : Continuous (fun t : ℝ => (1 - t^γ) * ∑ S : Finset (Fin n),
              ((D - 1 - S.card) * fourierCoeff (sectionDiff i (noise r (signField f))) S ^ 2) *
                t^S.card) :=
            (continuous_const.sub (Real.continuous_rpow_const hγ.le)).mul
              (continuous_spectral _)
          refine hcon.continuousOn.congr ?_
          intro t ht
          rw [Set.uIcc_of_le zero_le_one] at ht
          simp only [deficitIntegrand_eq D r f i ht.1]
        exact hc.intervalIntegrable
      · exact Continuous.intervalIntegrable (μ := MeasureTheory.volume)
          ((continuous_const.sub (Real.continuous_rpow_const hγ.le)).mul continuous_const) 0 1
      · intro t ht
        have h1 : 0 ≤ 1 - t^γ := by
          have := Real.rpow_le_one ht.1 ht.2 hγ.le
          linarith
        exact mul_le_mul_of_nonneg_left
          (deficitIntegrand_le hr₀ hr₁ hf i ha ht.1 ht.2) h1
    rw [intervalIntegral.integral_mul_const, integral_one_sub_rpow hγ] at hmono
    have hk := mul_le_mul_of_nonneg_left hmono (by positivity : 0 ≤ γ / (γ + D))
    calc γ / (γ + D) * ∫ t in (0:ℝ)..1, (1 - t^γ) * deficitIntegrand D r f i t
        ≤ γ / (γ + D) * (γ / (γ + 1) * B) := hk
      _ = lsiConst γ D * r^2 * pivotalMean i f ^ 2 := by
          rw [hB, lsiConst]; field_simp
  · rw [coordDeficit_eq_section, ← ha]
    have hz : ∀ S, fourierCoeff (sectionDiff i (noise r (signField f))) S = 0 := by
      intro S
      rw [sectionDiff_noise_signField]
      have : (fun x => r * noise r (pivotal i f) x) = fun _ => 0 := by
        funext x
        have hp : pivotal i f = fun _ => 0 := funext (pivotal_eq_zero_of_mean hf i ha.symm)
        rw [hp, noise_const, mul_zero]
      rw [this]; simp [fourierCoeff, cubeExpect]
    simp [hz]

/-! ### Second branch: Parseval for the pivotal indicator -/

theorem deficit_term_le {γ D r : ℝ} (hγ : 0 < γ) (hD : 2 ≤ D) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1)
    {k : ℕ} (hk : 2 ≤ k) :
    (degWeight γ D - degWeight γ k) / k * r^(2*k) ≤ deficitCoeff γ D r 2 / 2 := by
  have hk0 : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hd2 : 0 ≤ deficitCoeff γ D r 2 := by
    unfold deficitCoeff
    apply mul_nonneg _ (pow_nonneg hr₀ _)
    have := degWeight_mono hγ (by norm_num) (by exact_mod_cast hD : ((2:ℕ):ℝ) ≤ D)
    push_cast at this ⊢
    linarith
  by_cases hkD : (k:ℝ) ≤ D
  · have hA0 : 0 ≤ degWeight γ D - degWeight γ k :=
      sub_nonneg.mpr (degWeight_mono hγ (by linarith) hkD)
    have hA : degWeight γ D - degWeight γ k ≤ degWeight γ D - degWeight γ 2 := by
      have := degWeight_mono hγ (by norm_num) hk0
      linarith
    have hp : r^(2*k) ≤ r^(2*2) := pow_le_pow_of_le_one hr₀ hr₁ (by omega)
    unfold deficitCoeff
    push_cast
    calc (degWeight γ D - degWeight γ k) / k * r^(2*k)
        ≤ (degWeight γ D - degWeight γ k) / 2 * r^(2*k) := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr₀ _)
          exact div_le_div_of_nonneg_left hA0 (by norm_num) hk0
      _ ≤ (degWeight γ D - degWeight γ 2) / 2 * r^(2*2) := by
          apply mul_le_mul (by linarith) hp (pow_nonneg hr₀ _) (by
            have := degWeight_mono hγ (by norm_num) (by linarith : (2:ℝ) ≤ D)
            linarith)
      _ = (degWeight γ D - degWeight γ 2) * r^(2*2) / 2 := by ring
  · push Not at hkD
    have hA : degWeight γ D - degWeight γ k ≤ 0 :=
      sub_nonpos.mpr (degWeight_mono hγ (by linarith) hkD.le)
    have : (degWeight γ D - degWeight γ k) / k * r^(2*k) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hA (by linarith))
        (pow_nonneg hr₀ _)
    linarith

/-- Second branch: `D_i ≤ d_2/2 a_i + (d_1 - d_2/2) a_i^2`. -/
theorem coordDeficit_le_parseval {n : ℕ} {γ D r : ℝ} (hγ : 0 < γ) (hD : 2 ≤ D)
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) {f : Cube n → Bool} (hf : Monotone f) (i : Fin n) :
    coordDeficit γ D r f i ≤
      deficitCoeff γ D r 2 / 2 * pivotalMean i f +
        (deficitCoeff γ D r 1 - deficitCoeff γ D r 2 / 2) * pivotalMean i f ^ 2 := by
  classical
  have hbound : ∀ S : Finset (Fin n),
      (if i ∈ S then (degWeight γ D - degWeight γ S.card) / S.card *
        fourierCoeff (noise r (signField f)) S ^ 2 else 0) ≤
      deficitCoeff γ D r 2 / 2 *
          (if i ∈ S then fourierCoeff (signField f) S ^ 2 else 0) +
        (deficitCoeff γ D r 1 - deficitCoeff γ D r 2 / 2) *
          (if S = {i} then fourierCoeff (signField f) S ^ 2 else 0) := by
    intro S
    rw [fourierCoeff_noise, mul_pow, ← pow_mul]
    by_cases hS : S = {i}
    · subst hS
      simp only [Finset.mem_singleton, if_true, Finset.card_singleton, Nat.cast_one, div_one]
      unfold deficitCoeff
      push_cast
      ring_nf
      rfl
    · rw [if_neg hS, mul_zero, add_zero]
      split_ifs with hi
      · have hk : 2 ≤ S.card := by
          by_contra hlt
          push Not at hlt
          have h1 : 1 ≤ S.card := Finset.card_pos.mpr ⟨i, hi⟩
          have hc : S.card = 1 := by omega
          obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc
          subst hj
          simp at hi
          exact hS (by rw [hi])
        have ht := deficit_term_le hγ hD hr₀ hr₁ hk
        have := mul_le_mul_of_nonneg_right ht (sq_nonneg (fourierCoeff (signField f) S))
        calc (degWeight γ D - degWeight γ S.card) / S.card *
              (r ^ (S.card * 2) * fourierCoeff (signField f) S ^ 2)
            = (degWeight γ D - degWeight γ S.card) / S.card * r^(2*S.card) *
                fourierCoeff (signField f) S ^ 2 := by ring_nf
          _ ≤ _ := this
      · simp
  calc coordDeficit γ D r f i
      ≤ ∑ S : Finset (Fin n), (deficitCoeff γ D r 2 / 2 *
          (if i ∈ S then fourierCoeff (signField f) S ^ 2 else 0) +
        (deficitCoeff γ D r 1 - deficitCoeff γ D r 2 / 2) *
          (if S = {i} then fourierCoeff (signField f) S ^ 2 else 0)) :=
        Finset.sum_le_sum (fun S _ => hbound S)
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          sum_sq_fourierCoeff_mem hf i]
        simp [pivotalMean]

/-- `D_i ≤ D(a_i)`. -/
theorem coordDeficit_le_bound {n : ℕ} {γ D r : ℝ} (hγ : 0 < γ) (hD : 2 ≤ D) (hr₀ : 0 < r)
    (hr₁ : r ≤ 1) {f : Cube n → Bool} (hf : Monotone f) (i : Fin n) :
    coordDeficit γ D r f i ≤ deficitBound γ D r (pivotalMean i f) :=
  le_min (coordDeficit_le_lsi hγ hD hr₀ hr₁ hf i)
    (coordDeficit_le_parseval hγ hD hr₀.le hr₁ hf i)

/-! ### Summed spectral inequality -/

theorem variance_eq_fourier {n : ℕ} (u : Cube n → ℝ) :
    cubeExpect (fun x => u x ^ 2) - cubeExpect u ^ 2 =
      ∑ S : Finset (Fin n), if S = ∅ then 0 else fourierCoeff u S ^ 2 := by
  rw [parseval, sum_ite_empty, fourierCoeff_empty]

theorem sum_coordDeficit {n : ℕ} (γ D r : ℝ) (f : Cube n → Bool) :
    (∑ i, coordDeficit γ D r f i) = ∑ S : Finset (Fin n), if S = ∅ then 0 else
      (degWeight γ D - degWeight γ S.card) * fourierCoeff (noise r (signField f)) S ^ 2 := by
  unfold coordDeficit
  rw [sum_coord_mem (fun S => (degWeight γ D - degWeight γ S.card) / S.card *
    fourierCoeff (noise r (signField f)) S ^ 2)]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs with hS
  · simp [hS]
  · have hc : (0:ℝ) < S.card := by
      exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    field_simp

/-- The source's summed spectral inequality (eq:spectral). -/
theorem spectral_deficit {n : ℕ} {γ D r : ℝ} (hγ : 0 < γ) (hD : 2 ≤ D) (hr₀ : 0 < r)
    (hr₁ : r ≤ 1) {f : Cube n → Bool} (hf : Monotone f) :
    degWeight γ D * (cubeExpect (fun x => noise r (signField f) x ^ 2) -
        cubeExpect (noise r (signField f)) ^ 2) -
      ∑ i, deficitBound γ D r (pivotalMean i f) ≤
    ∑ S : Finset (Fin n), if S = ∅ then 0 else
      degWeight γ S.card * fourierCoeff (noise r (signField f)) S ^ 2 := by
  have hsum := sum_coordDeficit γ D r f
  have hle : (∑ i, coordDeficit γ D r f i) ≤ ∑ i, deficitBound γ D r (pivotalMean i f) :=
    Finset.sum_le_sum (fun i _ => coordDeficit_le_bound hγ hD hr₀ hr₁ hf i)
  have hid : degWeight γ D * (cubeExpect (fun x => noise r (signField f) x ^ 2) -
        cubeExpect (noise r (signField f)) ^ 2) -
      (∑ i, coordDeficit γ D r f i) =
      ∑ S : Finset (Fin n), if S = ∅ then 0 else
        degWeight γ S.card * fourierCoeff (noise r (signField f)) S ^ 2 := by
    rw [variance_eq_fourier, hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro S _
    split_ifs <;> ring
  linarith

end MostInformativeBit
