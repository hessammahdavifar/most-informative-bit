import MostInformativeBit.EntropyContraction
import Mathlib.Analysis.SpecialFunctions.Artanh

/-! Strict interior positivity and the actual entropy-flow derivative. -/
namespace MostInformativeBit
open scoped BigOperators

/-- Strict positivity of each BSC transition for an interior correlation. -/
theorem noiseKernel_pos {n : ℕ} {r : ℝ} (hr₀ : -1 < r) (hr₁ : r < 1) (x y : Cube n) :
    0 < GeneralCK.noiseKernel ((1-r)/2) x y := by
  unfold GeneralCK.noiseKernel
  apply Finset.prod_pos
  intro i _
  split_ifs <;> linarith

theorem noise_lt_constant {n : ℕ} {r b : ℝ} (hr₀ : -1 < r) (hr₁ : r < 1)
    {v : Cube n → ℝ} (hv : ∀ x, v x ≤ b) (hs : ∃ x, v x < b) (y : Cube n) :
    noise r v y < b := by
  have hh : noise r v y < noise r (fun _ => b) y := by
    apply Finset.sum_lt_sum
    · intro x _
      exact mul_le_mul_of_nonneg_left (hv x) (noiseKernel_pos hr₀ hr₁ x y).le
    · obtain ⟨x, hx⟩ := hs
      exact ⟨x, Finset.mem_univ x, mul_lt_mul_of_pos_left hx (noiseKernel_pos hr₀ hr₁ x y)⟩
  simpa only [noise_const] using hh

theorem constant_lt_noise {n : ℕ} {r a : ℝ} (hr₀ : -1 < r) (hr₁ : r < 1)
    {v : Cube n → ℝ} (hv : ∀ x, a ≤ v x) (hs : ∃ x, a < v x) (y : Cube n) :
    a < noise r v y := by
  have hh : noise r (fun _ => a) y < noise r v y := by
    apply Finset.sum_lt_sum
    · intro x _
      exact mul_le_mul_of_nonneg_left (hv x) (noiseKernel_pos hr₀ hr₁ x y).le
    · obtain ⟨x, hx⟩ := hs
      exact ⟨x, Finset.mem_univ x, mul_lt_mul_of_pos_left hx (noiseKernel_pos hr₀ hr₁ x y)⟩
  simpa only [noise_const] using hh

/-- Nonconstant Boolean rules are strictly inside the sign interval after nontrivial noise. -/
theorem noise_signField_mem_Ioo {n : ℕ} {r : ℝ} (hr₀ : -1 < r) (hr₁ : r < 1)
    {f : Cube n → Bool} (hf : ∃ x y, f x ≠ f y) (z : Cube n) :
    noise r (signField f) z ∈ Set.Ioo (-1) 1 := by
  obtain ⟨x, y, hxy⟩ := hf
  have hb : (f x = false ∧ f y = true) ∨ (f x = true ∧ f y = false) := by
    cases hx : f x <;> cases hy : f y <;> simp_all
  have hex₀ : ∃ x, signField f x < 1 := by
    rcases hb with h | h
    · exact ⟨x, by norm_num [signField, h.1, cubeSign]⟩
    · exact ⟨y, by norm_num [signField, h.2, cubeSign]⟩
  have hex₁ : ∃ x, -1 < signField f x := by
    rcases hb with h | h
    · exact ⟨y, by norm_num [signField, h.2, cubeSign]⟩
    · exact ⟨x, by norm_num [signField, h.1, cubeSign]⟩
  exact ⟨constant_lt_noise hr₀ hr₁ (fun x => (signField_mem_Icc f x).1) hex₁ z,
    noise_lt_constant hr₀ hr₁ (fun x => (signField_mem_Icc f x).2) hex₀ z⟩

/-- The derivative of phi on the interior of its natural domain. -/
theorem phi_hasDerivAt {t : ℝ} (ht₀ : -1 < t) (ht₁ : t < 1) :
    HasDerivAt phi (Real.artanh t) t := by
  have ha : HasDerivAt (fun s : ℝ => (1-s)/2) (-1/2) t := by
    simpa using ((hasDerivAt_id t).const_sub 1).div_const 2
  have hb := (Real.hasDerivAt_binEntropy (by linarith : (1-t)/2 ≠ 0)
    (by linarith : (1-t)/2 ≠ 1)).comp t ha
  have hc := hb.const_sub (Real.log 2)
  change HasDerivAt (fun s => Real.log 2 - Real.binEntropy ((1-s)/2)) (Real.artanh t) t
  apply hc.congr_deriv
  rw [show 1-(1-t)/2 = (1+t)/2 by ring,
    Real.artanh_eq_half_log ⟨ht₀.le, ht₁.le⟩,
    Real.log_div (by linarith : 1+t ≠ 0) (by norm_num : (2:ℝ) ≠ 0),
    Real.log_div (by linarith : 1-t ≠ 0) (by norm_num : (2:ℝ) ≠ 0),
    Real.log_div (by linarith : 1+t ≠ 0) (by linarith : 1-t ≠ 0)]
  ring

/-- The entropy-production action A(u) in mechanism.tex. -/
noncomputable def entropyAction {n : ℕ} (v : Cube n → ℝ) : ℝ :=
  cubeExpect (fun x => Real.artanh (v x) * cubeLaplacian v x)

/-- Entropy flow for any real field whose smoothed values are interior. -/
theorem phiEntropy_noise_hasDerivAt {n : ℕ} (v : Cube n → ℝ) {r : ℝ} (hr : r ≠ 0)
    (hv : ∀ x, noise r v x ∈ Set.Ioo (-1) 1) :
    HasDerivAt (fun t => phiEntropy (noise t v)) (entropyAction (noise r v) / r) r := by
  have hd (x : Cube n) := (phi_hasDerivAt (hv x).1 (hv x).2).comp r
    (noise_hasDerivAt_laplacian v x hr)
  have hs := ((HasDerivAt.fun_sum (u := Finset.univ) (fun x _ => hd x)).const_mul
    (GeneralCK.Information.cubeWeight n)).sub_const (phi (cubeExpect v))
  simp only [phiEntropy, cubeExpect_noise]
  simpa only [Function.comp_apply, cubeExpect, entropyAction,
    mul_div_assoc, Finset.sum_div] using hs

/-- The manuscript's entropy-flow identity for every nonconstant Boolean rule. -/
theorem information_entropy_flow {n : ℕ} {f : Cube n → Bool} (hf : ∃ x y, f x ≠ f y)
    {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    r * deriv (information f) r = entropyAction (noise r (signField f)) := by
  have hd := phiEntropy_noise_hasDerivAt (signField f) (ne_of_gt hr₀)
    (noise_signField_mem_Ioo (by linarith) hr₁ hf)
  have he : information f = fun t => phiEntropy (noise t (signField f)) :=
    funext (information_eq_phiEntropy f)
  rw [he, hd.deriv]
  field_simp

end MostInformativeBit
