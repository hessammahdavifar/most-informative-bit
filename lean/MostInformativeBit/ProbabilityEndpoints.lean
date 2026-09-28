import MostInformativeBit.Definitions

namespace MostInformativeBit
open scoped BigOperators

theorem kernel_zero {n : ℕ} (x y : Cube n) :
    GeneralCK.noiseKernel 0 x y = if x = y then 1 else 0 := by
  classical
  simp only [GeneralCK.noiseKernel, sub_zero, Fintype.prod_ite_zero,
    Finset.prod_const_one, funext_iff]

theorem posterior_zero {n : ℕ} (f : Cube n → Bool) (y : Cube n) :
    GeneralCK.Information.posterior f 0 y = if f y then 1 else 0 := by
  classical
  unfold GeneralCK.Information.posterior
  simp_rw [kernel_zero]
  have ht : ∀ x : Cube n,
      (if f x = true then if x = y then (1:ℝ) else 0 else 0) =
        if x = y then (if f y then 1 else 0) else 0 := by
    intro x
    by_cases he : x = y
    · subst x; simp
    · simp [he]
  simp_rw [ht]
  simp

theorem information_one {n : ℕ} (f : Cube n → Bool) :
    information f 1 = Real.binEntropy (GeneralCK.Information.meanIndicator f) := by
  rw [information_eq_conditional_entropy]
  norm_num
  have he : ∀ y : Cube n,
      Real.binEntropy (GeneralCK.Information.posterior f 0 y) = 0 := by
    intro y
    rw [posterior_zero]
    cases f y <;> simp
  simp_rw [he]
  simp

theorem gap_one_nonpos {n : ℕ} (f : Cube n → Bool) : gap f 1 ≤ 0 := by
  rw [gap, information_one]
  simpa [phi, h] using
    (sub_nonneg.mpr (Real.binEntropy_le_log_two
      (p := GeneralCK.Information.meanIndicator f)))

theorem kernel_continuous {n : ℕ} (x y : Cube n) :
    Continuous (fun p : ℝ => GeneralCK.noiseKernel p x y) := by
  unfold GeneralCK.noiseKernel
  apply continuous_finsetProd
  intro i _
  split_ifs <;> fun_prop

theorem posterior_continuous {n : ℕ} (f : Cube n → Bool) (y : Cube n) :
    Continuous (fun p : ℝ => GeneralCK.Information.posterior f p y) := by
  unfold GeneralCK.Information.posterior
  apply continuous_finsetSum
  intro x _
  split_ifs
  · exact kernel_continuous x y
  · fun_prop

theorem information_continuous {n : ℕ} (f : Cube n → Bool) :
    Continuous (information f) := by
  have he : information f = fun r =>
      Real.binEntropy (GeneralCK.Information.meanIndicator f) -
      GeneralCK.Information.cubeWeight n *
        ∑ y, Real.binEntropy (GeneralCK.Information.posterior f ((1-r)/2) y) :=
    funext (information_eq_conditional_entropy f)
  rw [he]
  apply Continuous.sub continuous_const
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro y _
  exact Real.binEntropy_continuous.comp
    ((posterior_continuous f y).comp (by fun_prop))

theorem gap_continuous {n : ℕ} (f : Cube n → Bool) : Continuous (gap f) := by
  unfold gap phi h
  exact (information_continuous f).sub
    (continuous_const.sub (Real.binEntropy_continuous.comp (by fun_prop)))

end MostInformativeBit
