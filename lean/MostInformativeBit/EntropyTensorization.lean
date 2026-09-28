import MostInformativeBit.EntropyContraction

/-! Unconditional proof of the cube entropy contraction (S6a):
`cubeEntropy (noise r w) ≤ r^2 * cubeEntropy w` for every dimension, every
nonnegative field `w`, and every correlation `-1 ≤ r ≤ 1`.

Route: split off the first coordinate. The entropy chain rule, convexity of
entropy (from the Gibbs inequality) and the induction hypothesis handle the
remaining coordinates; the sharp two-point contraction is proved from the
power series of the logarithm. Strict positivity is removed by an epsilon
limit. No log-Sobolev inequality is assumed. -/
namespace MostInformativeBit
open scoped BigOperators
open Real

/-! ### Splitting off the first coordinate -/

theorem sum_cube_succ {n : ℕ} (g : Cube (n+1) → ℝ) :
    ∑ x, g x = ∑ y : Cube n, g (Fin.cons false y) + ∑ y : Cube n, g (Fin.cons true y) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp, Fintype.sum_prod_type,
    Fintype.sum_bool, add_comm]
  rfl

theorem cubeWeight_succ (n : ℕ) :
    GeneralCK.Information.cubeWeight (n+1) = GeneralCK.Information.cubeWeight n / 2 := by
  simp only [GeneralCK.Information.cubeWeight, zpow_neg, zpow_natCast, pow_succ]
  field_simp

theorem cubeExpect_succ {n : ℕ} (v : Cube (n+1) → ℝ) :
    cubeExpect v = (cubeExpect (fun y : Cube n => v (Fin.cons false y)) +
      cubeExpect (fun y : Cube n => v (Fin.cons true y))) / 2 := by
  simp only [cubeExpect, sum_cube_succ v, cubeWeight_succ]
  ring

theorem noiseKernel_cons {n : ℕ} (p : ℝ) (b c : Bool) (x y : Cube n) :
    GeneralCK.noiseKernel p (Fin.cons b x : Cube (n+1)) (Fin.cons c y) =
      (if b = c then 1 - p else p) * GeneralCK.noiseKernel p x y := by
  simp [GeneralCK.noiseKernel, Fin.prod_univ_succ]

theorem noise_cons_false {n : ℕ} (r : ℝ) (w : Cube (n+1) → ℝ) (z : Cube n) :
    noise r w (Fin.cons false z) =
      (1+r)/2 * noise r (fun y => w (Fin.cons false y)) z +
      (1-r)/2 * noise r (fun y => w (Fin.cons true y)) z := by
  simp only [noise, sum_cube_succ, noiseKernel_cons, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro y _ <;> simp <;> ring

theorem noise_cons_true {n : ℕ} (r : ℝ) (w : Cube (n+1) → ℝ) (z : Cube n) :
    noise r w (Fin.cons true z) =
      (1-r)/2 * noise r (fun y => w (Fin.cons false y)) z +
      (1+r)/2 * noise r (fun y => w (Fin.cons true y)) z := by
  simp only [noise, sum_cube_succ, noiseKernel_cons, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro y _ <;> simp <;> ring

/-! ### Entropy chain rule -/

/-- Entropy of the uniform two-point measure carrying the values `a` and `b`. -/
noncomputable def pairEntropy (a b : ℝ) : ℝ :=
  (a * log a + b * log b) / 2 - (a + b) / 2 * log ((a + b) / 2)

/-- Exact chain rule for the first coordinate. No positivity is needed. -/
theorem cubeEntropy_succ {n : ℕ} (u : Cube (n+1) → ℝ) :
    cubeEntropy u =
      pairEntropy (cubeExpect (fun y : Cube n => u (Fin.cons false y)))
        (cubeExpect (fun y : Cube n => u (Fin.cons true y))) +
      (cubeEntropy (fun y : Cube n => u (Fin.cons false y)) +
        cubeEntropy (fun y : Cube n => u (Fin.cons true y))) / 2 := by
  rw [cubeEntropy_eq_mul_log, cubeEntropy_eq_mul_log, cubeEntropy_eq_mul_log,
    cubeExpect_succ u, cubeExpect_succ (fun x => u x * log (u x))]
  unfold pairEntropy
  ring

/-! ### Gibbs inequality and convexity of entropy -/

theorem cubeExpect_pos {n : ℕ} {v : Cube n → ℝ} (hv : ∀ x, 0 < v x) :
    0 < cubeExpect v := by
  apply mul_pos (by unfold GeneralCK.Information.cubeWeight; positivity)
  exact Finset.sum_pos (fun x _ => hv x) Finset.univ_nonempty

/-- Gibbs inequality: `log q` is a feasible test function in the variational
formula for entropy. Zeros of `u` are allowed where `q` vanishes. -/
theorem gibbs {n : ℕ} {u q : Cube n → ℝ} (hu : ∀ x, 0 ≤ u x) (hq : ∀ x, 0 ≤ q x)
    (hsupp : ∀ x, 0 < u x → 0 < q x) (hU : 0 < cubeExpect u) (hQ : 0 < cubeExpect q) :
    cubeExpect (fun x => u x * log (q x)) - cubeExpect u * log (cubeExpect q) ≤
      cubeExpect (fun x => u x * log (u x)) - cubeExpect u * log (cubeExpect u) := by
  set c := cubeExpect u / cubeExpect q with hc
  have hc0 : 0 < c := div_pos hU hQ
  have hpt : ∀ x, u x * log c + u x - c * q x ≤ u x * log (u x) - u x * log (q x) := by
    intro x
    rcases (hu x).lt_or_eq with hux | hux
    · have hqx := hsupp x hux
      have hl := Real.log_le_sub_one_of_pos (div_pos (mul_pos hc0 hqx) hux)
      rw [Real.log_div (mul_pos hc0 hqx).ne' hux.ne', Real.log_mul hc0.ne' hqx.ne'] at hl
      have := mul_le_mul_of_nonneg_left hl hux.le
      have he : u x * (c * q x / u x - 1) = c * q x - u x := by field_simp
      nlinarith
    · rw [← hux]
      nlinarith [mul_nonneg hc0.le (hq x)]
  have hs := cubeExpect_mono hpt
  rw [cubeExpect_sub, cubeExpect_sub, cubeExpect_add, cubeExpect_mul] at hs
  have hlin : cubeExpect (fun x => u x * log c) = cubeExpect u * log c := by
    rw [show (fun x => u x * log c) = fun x => log c * u x by ext x; ring, cubeExpect_mul]
    ring
  rw [hlin] at hs
  have hcq : c * cubeExpect q = cubeExpect u := by rw [hc]; field_simp
  have hlog : log c = log (cubeExpect u) - log (cubeExpect q) := Real.log_div hU.ne' hQ.ne'
  rw [hcq, hlog] at hs
  nlinarith

theorem noise_pos {n : ℕ} {r : ℝ} (hr₀ : -1 ≤ r) (hr₁ : r ≤ 1)
    {v : Cube n → ℝ} (hv : ∀ x, 0 < v x) (y : Cube n) : 0 < noise r v y := by
  have hk := GeneralCK.Information.kernel_column_sum ((1-r)/2) y
  obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hk.symm ▸ one_ne_zero)
  have hk0 : ∀ x, 0 ≤ GeneralCK.noiseKernel ((1-r)/2) x y :=
    fun x => GeneralCK.noiseKernel_nonneg (by linarith) (by linarith) x y
  apply Finset.sum_pos' (fun x _ => mul_nonneg (hk0 x) (hv x).le)
  exact ⟨x, Finset.mem_univ x, mul_pos (lt_of_le_of_ne (hk0 x) (Ne.symm hx)) (hv x)⟩

/-- Convexity of entropy along a two-point mixture of positive fields. -/
theorem cubeEntropy_mix_le {n : ℕ} {u v : Cube n → ℝ} (hu : ∀ x, 0 < u x)
    (hv : ∀ x, 0 < v x) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    cubeEntropy (fun x => t * u x + (1-t) * v x) ≤
      t * cubeEntropy u + (1-t) * cubeEntropy v := by
  set q : Cube n → ℝ := fun x => t * u x + (1-t) * v x with hqdef
  have hq : ∀ x, 0 < q x := by
    intro x
    have h1 := min_le_left (u x) (v x)
    have h2 := min_le_right (u x) (v x)
    have h3 : 0 < min (u x) (v x) := lt_min (hu x) (hv x)
    simp only [hqdef]
    nlinarith
  have gu := gibbs (fun x => (hu x).le) (fun x => (hq x).le) (fun x _ => hq x)
    (cubeExpect_pos hu) (cubeExpect_pos hq)
  have gv := gibbs (fun x => (hv x).le) (fun x => (hq x).le) (fun x _ => hq x)
    (cubeExpect_pos hv) (cubeExpect_pos hq)
  have hEq : cubeExpect q = t * cubeExpect u + (1-t) * cubeExpect v := by
    rw [hqdef, cubeExpect_add, cubeExpect_mul, cubeExpect_mul]
  have hEql : cubeExpect (fun x => q x * log (q x)) =
      t * cubeExpect (fun x => u x * log (q x)) +
        (1-t) * cubeExpect (fun x => v x * log (q x)) := by
    rw [← cubeExpect_mul, ← cubeExpect_mul, ← cubeExpect_add]
    congr 1; ext x; simp only [hqdef]; ring
  rw [cubeEntropy_eq_mul_log, cubeEntropy_eq_mul_log, cubeEntropy_eq_mul_log, hEql, hEq]
  rw [hEq] at gu gv
  have h1 := mul_le_mul_of_nonneg_left gu ht₀
  have h2 := mul_le_mul_of_nonneg_left gv (by linarith : (0:ℝ) ≤ 1-t)
  nlinarith

/-! ### Sharp two-point contraction -/

/-- Normalized two-point entropy with mean one. -/
noncomputable def pairF (s : ℝ) : ℝ := ((1+s) * log (1+s) + (1-s) * log (1-s)) / 2

theorem hasSum_pairF {s : ℝ} (hs : |s| < 1) :
    HasSum (fun k : ℕ => s ^ (2*k+2) / ((2*k+1) * (2*k+2))) (pairF s) := by
  have hs2 : |s^2| < 1 := by
    rw [abs_pow, sq_lt_one_iff₀ (abs_nonneg s)]; exact hs
  have hterm : ∀ k : ℕ, s ^ (2*k+2) / ((2*k+1) * (2*k+2)) =
      s/2 * (2 * (1 / (2*(k:ℝ)+1)) * s^(2*k+1)) + -1/2 * ((s^2)^(k+1) / ((k:ℝ)+1)) := by
    intro k
    have hk1 : (0:ℝ) < 2*k+1 := by positivity
    have hk2 : (0:ℝ) < (k:ℝ)+1 := by positivity
    rw [← pow_mul, show 2*(k+1) = 2*k+2 by ring, show s ^ (2*k+2) = s * s^(2*k+1) by ring]
    field_simp
    ring
  have h1 := (Real.hasSum_pow_div_log_of_abs_lt_one hs2).mul_left (-1/2)
  have h2 := (Real.hasSum_log_sub_log_of_abs_lt_one hs).mul_left (s/2)
  have h3 := h2.add h1
  have hp : 0 < 1 + s := by linarith [neg_abs_le s]
  have hm : 0 < 1 - s := by linarith [le_abs_self s]
  have hv : s/2 * (log (1+s) - log (1-s)) + -1/2 * -log (1 - s^2) = pairF s := by
    rw [show 1 - s^2 = (1+s) * (1-s) by ring, Real.log_mul hp.ne' hm.ne']
    unfold pairF; ring
  rw [hv] at h3
  have hfun : (fun k : ℕ => s ^ (2*k+2) / ((2*k+1) * (2*k+2))) = fun k : ℕ =>
      s/2 * (2 * (1 / (2*(k:ℝ)+1)) * s^(2*k+1)) + -1/2 * ((s^2)^(k+1) / ((k:ℝ)+1)) := by
    ext k
    exact hterm k
  rw [hfun]
  exact h3

theorem pairF_mul_le {s r : ℝ} (hs : |s| < 1) (hr : r^2 ≤ 1) :
    pairF (r*s) ≤ r^2 * pairF s := by
  have hr' : |r| ≤ 1 := by rwa [← sq_le_one_iff_abs_le_one]
  have hrs : |r*s| < 1 := by
    rw [abs_mul]
    calc |r| * |s| ≤ 1 * |s| := by gcongr
      _ < 1 := by linarith
  refine hasSum_le (fun k => ?_) (hasSum_pairF hrs) ((hasSum_pairF hs).mul_left (r^2))
  have hk : (0:ℝ) < (2*k+1) * (2*k+2) := by positivity
  have hpow : (r*s)^(2*k+2) = (r^2)^(k+1) * (s^2)^(k+1) := by ring
  have hs2 : s^(2*k+2) = (s^2)^(k+1) := by ring
  have hle : (r^2)^(k+1) ≤ r^2 := by
    rw [pow_succ']
    exact mul_le_of_le_one_right (sq_nonneg r) (pow_le_one₀ (sq_nonneg r) hr)
  rw [hpow, hs2, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hk.le
  exact mul_le_mul_of_nonneg_right hle (pow_nonneg (sq_nonneg s) _)

theorem pairEntropy_scale {m t : ℝ} (hm : 0 < m) (ht : |t| < 1) :
    pairEntropy (m*(1+t)) (m*(1-t)) = m * pairF t := by
  have hp : 0 < 1 + t := by linarith [neg_abs_le t]
  have hq : 0 < 1 - t := by linarith [le_abs_self t]
  unfold pairEntropy pairF
  rw [show (m*(1+t) + m*(1-t))/2 = m by ring, Real.log_mul hm.ne' hp.ne',
    Real.log_mul hm.ne' hq.ne']
  ring

/-- Sharp one-coordinate entropy contraction of the BSC with correlation `r`. -/
theorem pairEntropy_noise_le {a b r : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hr₀ : -1 ≤ r) (hr₁ : r ≤ 1) :
    pairEntropy ((1+r)/2 * a + (1-r)/2 * b) ((1-r)/2 * a + (1+r)/2 * b) ≤
      r^2 * pairEntropy a b := by
  set m := (a+b)/2 with hm
  set s := (a-b)/(a+b) with hsdef
  have hm0 : 0 < m := by positivity
  have hab : 0 < a + b := by positivity
  have hs : |s| < 1 := by
    rw [abs_lt, hsdef]
    constructor
    · rw [lt_div_iff₀ hab]; linarith
    · rw [div_lt_iff₀ hab]; linarith
  have ea : a = m*(1+s) := by rw [hm, hsdef]; field_simp; ring
  have eb : b = m*(1-s) := by rw [hm, hsdef]; field_simp; ring
  have e1 : (1+r)/2 * a + (1-r)/2 * b = m*(1+r*s) := by rw [ea, eb]; ring
  have e2 : (1-r)/2 * a + (1+r)/2 * b = m*(1-r*s) := by rw [ea, eb]; ring
  have hr2 : r^2 ≤ 1 := by nlinarith
  have hrs : |r*s| < 1 := by
    rw [abs_mul]
    have : |r| ≤ 1 := abs_le.mpr ⟨hr₀, hr₁⟩
    calc |r| * |s| ≤ 1 * |s| := by gcongr
      _ < 1 := by linarith
  rw [e1, e2, pairEntropy_scale hm0 hrs]
  conv_rhs => rw [ea, eb, pairEntropy_scale hm0 hs]
  have := pairF_mul_le hs hr2
  nlinarith

/-! ### Tensorization by induction on the dimension -/

theorem cubeEntropy_dim_zero (v : Cube 0 → ℝ) : cubeEntropy v = 0 := by
  have hv : v = fun _ => v (fun i => Fin.elim0 i) := by
    funext x; congr 1; funext i; exact Fin.elim0 i
  rw [hv, cubeEntropy_const]

theorem cubeEntropy_noise_le_of_pos {r : ℝ} (hr₀ : -1 ≤ r) (hr₁ : r ≤ 1) :
    ∀ (n : ℕ) (w : Cube n → ℝ), (∀ x, 0 < w x) →
      cubeEntropy (noise r w) ≤ r^2 * cubeEntropy w := by
  intro n
  induction n with
  | zero => intro w _; simp [cubeEntropy_dim_zero]
  | succ n ih =>
    intro w hw
    set f0 : Cube n → ℝ := fun y => w (Fin.cons false y) with hf0
    set f1 : Cube n → ℝ := fun y => w (Fin.cons true y) with hf1
    have hp0 : ∀ y, 0 < f0 y := fun y => hw _
    have hp1 : ∀ y, 0 < f1 y := fun y => hw _
    have hn0 : (fun y : Cube n => noise r w (Fin.cons false y)) =
        fun y => (1+r)/2 * noise r f0 y + (1 - (1+r)/2) * noise r f1 y := by
      funext y; rw [noise_cons_false]; ring
    have hn1 : (fun y : Cube n => noise r w (Fin.cons true y)) =
        fun y => (1-r)/2 * noise r f0 y + (1 - (1-r)/2) * noise r f1 y := by
      funext y; rw [noise_cons_true]; ring
    have hT0 := noise_pos hr₀ hr₁ hp0
    have hT1 := noise_pos hr₀ hr₁ hp1
    -- one-coordinate part
    have hE0 : cubeExpect (fun y : Cube n => noise r w (Fin.cons false y)) =
        (1+r)/2 * cubeExpect f0 + (1-r)/2 * cubeExpect f1 := by
      rw [hn0, cubeExpect_add, cubeExpect_mul, cubeExpect_mul, cubeExpect_noise,
        cubeExpect_noise]; ring
    have hE1 : cubeExpect (fun y : Cube n => noise r w (Fin.cons true y)) =
        (1-r)/2 * cubeExpect f0 + (1+r)/2 * cubeExpect f1 := by
      rw [hn1, cubeExpect_add, cubeExpect_mul, cubeExpect_mul, cubeExpect_noise,
        cubeExpect_noise]; ring
    have hpair := pairEntropy_noise_le (cubeExpect_pos hp0) (cubeExpect_pos hp1) hr₀ hr₁
    -- remaining coordinates: convexity and the induction hypothesis
    have hc0 := cubeEntropy_mix_le hT0 hT1 (t := (1+r)/2) (by linarith) (by linarith)
    have hc1 := cubeEntropy_mix_le hT0 hT1 (t := (1-r)/2) (by linarith) (by linarith)
    have hi0 := ih f0 hp0
    have hi1 := ih f1 hp1
    rw [cubeEntropy_succ (noise r w), cubeEntropy_succ w, hE0, hE1, hn0, hn1]
    nlinarith

/-! ### Removing strict positivity -/

theorem continuous_cubeEntropy_add_const {n : ℕ} (v : Cube n → ℝ) :
    Continuous (fun ε : ℝ => cubeEntropy (fun x => v x + ε)) := by
  unfold cubeEntropy cubeExpect
  fun_prop

/-- (S6a), ordinary entropy form: Gross entropy contraction on the cube,
proved for every dimension, nonnegative field, and `-1 ≤ r ≤ 1`. -/
theorem cubeEntropy_noise_le {n : ℕ} {r : ℝ} (hr₀ : -1 ≤ r) (hr₁ : r ≤ 1)
    {w : Cube n → ℝ} (hw : ∀ x, 0 ≤ w x) :
    cubeEntropy (noise r w) ≤ r^2 * cubeEntropy w := by
  set g : ℝ → ℝ := fun ε =>
    r^2 * cubeEntropy (fun x => w x + ε) - cubeEntropy (fun x => noise r w x + ε) with hg
  have hcont : Continuous g :=
    (continuous_const.mul (continuous_cubeEntropy_add_const w)).sub
      (continuous_cubeEntropy_add_const (noise r w))
  have hpos : ∀ ε > 0, 0 ≤ g ε := by
    intro ε hε
    have h := cubeEntropy_noise_le_of_pos hr₀ hr₁ n (fun x => w x + ε)
      (fun x => by linarith [hw x])
    rw [noise_add, noise_const] at h
    simp only [hg]
    linarith
  have h0 : 0 ≤ g 0 := by
    refine ge_of_tendsto ((hcont.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))) ?_
    exact eventually_nhdsWithin_of_forall (fun ε (hε : ε ∈ Set.Ioi 0) => hpos ε hε)
  simp only [hg, add_zero] at h0
  linarith

theorem cubeEntropyContraction_holds {n : ℕ} {r : ℝ} (hr₀ : -1 ≤ r) (hr₁ : r ≤ 1) :
    CubeEntropyContraction n r :=
  fun _ hw => cubeEntropy_noise_le hr₀ hr₁ hw

/-- (S6a), phi-entropy form, via the Fourier worker's exact bridge. -/
theorem phiEntropyContraction_holds {n : ℕ} {r : ℝ} (hr₀ : -1 ≤ r) (hr₁ : r ≤ 1) :
    PhiEntropyContraction n r :=
  phiEntropyContraction_of_cubeEntropyContraction (cubeEntropyContraction_holds hr₀ hr₁)

/-- The manuscript's statement (S6a) for `0 ≤ r ≤ 1`. -/
theorem S6a {n : ℕ} {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) {w : Cube n → ℝ}
    (hw : ∀ x, 0 ≤ w x) : cubeEntropy (noise r w) ≤ r^2 * cubeEntropy w :=
  cubeEntropy_noise_le (by linarith) hr₁ hw

end MostInformativeBit
