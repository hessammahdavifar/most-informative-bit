import MostInformativeBit.CenteredSupport
import MostInformativeBit.EntropyContraction

namespace MostInformativeBit
open scoped BigOperators

/-- Completing the square in each actual Fourier coordinate. -/
theorem spectral_square_bound {n : ℕ} (u v : Cube n → ℝ) {gamma lam : ℝ}
    (hg : 0 < gamma) :
    2*lam*(gamma+1)*cubeExpect (fun x => u x*v x) -
      gamma*cubeExpect (fun x => v x^2) ≤
    cubeExpect (fun x => v x*cubeLaplacian v x) +
      lam^2*(gamma+1)^2 *
        ∑ S : Finset (Fin n), fourierCoeff u S^2/(gamma+S.card) := by
  rw [fourier_inner, parseval, laplacian_energy]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro S _
  have hd : 0 < gamma+(S.card:ℝ) := by positivity
  apply (mul_le_mul_iff_right₀ hd).mp
  have hs := sq_nonneg ((gamma+S.card)*fourierCoeff v S-lam*(gamma+1)*fourierCoeff u S)
  field_simp
  nlinarith

/-- The averaged support inequality in a form adapted to Fourier square completion. -/
theorem averaged_centered_support {n : ℕ} (u : Cube n → ℝ)
    {ell : ℝ} (hell : 31/20 ≤ ell) (hu : ∀ x, u x ∈ Set.Icc (-1) 1) :
    let r := Real.tanh ell
    let theta := Real.arcsin r
    let lam := theta/r
    let alpha := (theta+Real.sinh ell)/ell
    let gamma := lam*alpha
    gamma*cubeExpect (fun x => (Real.arcsin (u x))^2) -
        2*lam*(gamma+1)*cubeExpect (fun x => u x*Real.arcsin (u x)) +
        gamma*lam^2*cubeExpect (fun x => u x^2) ≤
      -2*theta^2-2*gamma*(cubeExpect (fun x => phi (u x))-phi r) := by
  intro r theta lam alpha gamma
  have he : 0 < ell := by linarith
  have hr : 0 < r := CenteredSupport.tanh_pos he
  have ht : 0 < theta := Real.arcsin_pos.mpr hr
  have hl : 0 < lam := div_pos ht hr
  have hs := cubeExpect_mono (fun x => mul_le_mul_of_nonneg_left
    (CenteredSupport.centered_support hell (hu x)) (show 0 ≤ 2*lam by positivity))
  have hident (x : Cube n) :
      2*lam*((alpha/2)*(Real.arcsin (u x)-lam*u x)^2) =
      gamma*(Real.arcsin (u x))^2 -
        (2*gamma*lam)*(u x*Real.arcsin (u x)) + (gamma*lam^2)*(u x^2) := by
    dsimp [gamma]; ring
  have hident' (x : Cube n) :
      2*lam*(u x*Real.arcsin (u x)-r*theta-alpha*(phi (u x)-phi r)) =
      (2*lam)*(u x*Real.arcsin (u x))-2*theta^2-
        (2*gamma)*(phi (u x)-phi r) := by
    dsimp [gamma, lam]; field_simp
  change cubeExpect (fun x => 2*lam*((alpha/2)*(Real.arcsin (u x)-lam*u x)^2)) ≤
    cubeExpect (fun x => 2*lam*(u x*Real.arcsin (u x)-r*theta-alpha*(phi (u x)-phi r))) at hs
  simp_rw [hident, hident', cubeExpect_add, cubeExpect_sub, cubeExpect_mul, cubeExpect_const] at hs
  simp only [cubeExpect_sub, cubeExpect_const] at hs
  nlinarith

/-- Centered resolvent bound, written as the finite spectral sum defining the resolvent. -/
theorem angular_resolvent {n : ℕ} (u : Cube n → ℝ)
    {ell : ℝ} (hell : 31/20 ≤ ell) (hu : ∀ x, u x ∈ Set.Icc (-1) 1) :
    let r := Real.tanh ell
    let theta := Real.arcsin r
    let lam := theta/r
    let alpha := (theta+Real.sinh ell)/ell
    let gamma := lam*alpha
    2*theta^2+2*gamma*(cubeExpect (fun x => phi (u x))-phi r) +
      lam^2 * ∑ S : Finset (Fin n),
        (gamma-(gamma+1)^2/(gamma+S.card))*fourierCoeff u S^2 ≤
    cubeExpect (fun x => Real.arcsin (u x) *
      cubeLaplacian (fun y => Real.arcsin (u y)) x) := by
  intro r theta lam alpha gamma
  have he : 0 < ell := by linarith
  have hr : 0 < r := CenteredSupport.tanh_pos he
  have ht : 0 < theta := Real.arcsin_pos.mpr hr
  have hl : 0 < lam := div_pos ht hr
  have ha : 0 < alpha := div_pos
    (add_pos ht (Real.sinh_pos_iff.mpr he)) he
  have hg : 0 < gamma := mul_pos hl ha
  have hs := averaged_centered_support u hell hu
  have hsq := spectral_square_bound u (fun x => Real.arcsin (u x)) (lam := lam) hg
  change gamma*cubeExpect (fun x => (Real.arcsin (u x))^2) -
      2*lam*(gamma+1)*cubeExpect (fun x => u x*Real.arcsin (u x)) +
      gamma*lam^2*cubeExpect (fun x => u x^2) ≤
    -2*theta^2-2*gamma*(cubeExpect (fun x => phi (u x))-phi r) at hs
  have hid :
      lam^2 * ∑ S : Finset (Fin n),
          (gamma-(gamma+1)^2/(gamma+S.card))*fourierCoeff u S^2 =
      gamma*lam^2*cubeExpect (fun x => u x^2) -
        lam^2*(gamma+1)^2*∑ S : Finset (Fin n), fourierCoeff u S^2/(gamma+S.card) := by
    rw [parseval]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro S _
    ring
  rw [hid]
  linarith

/-- The manuscript's information-gap form for the actual BSC posterior field. -/
theorem boolean_angular_resolvent {n : ℕ} (f : Cube n → Bool)
    {ell : ℝ} (hell : 31/20 ≤ ell) :
    let r := Real.tanh ell
    let u := noise r (signField f)
    let theta := Real.arcsin r
    let lam := theta/r
    let alpha := (theta+Real.sinh ell)/ell
    let gamma := lam*alpha
    2*theta^2+2*gamma*(phi (cubeExpect (signField f))+gap f r) +
      lam^2 * ∑ S : Finset (Fin n),
        (gamma-(gamma+1)^2/(gamma+S.card))*fourierCoeff u S^2 ≤
    cubeExpect (fun x => Real.arcsin (u x) *
      cubeLaplacian (fun y => Real.arcsin (u y)) x) := by
  intro r u theta lam alpha gamma
  have he : 0 < ell := by linarith
  have hr : 0 < r := CenteredSupport.tanh_pos he
  have hu : ∀ x, u x ∈ Set.Icc (-1) 1 := by
    apply noise_mem_Icc (by linarith) (Real.tanh_lt_one ell).le
    intro x
    cases hfx : f x <;> norm_num [signField, cubeSign, hfx]
  have hh := angular_resolvent u hell hu
  have hi : cubeExpect (fun x => phi (u x))-phi r =
      phi (cubeExpect (signField f))+gap f r := by
    rw [gap, information_eq_phiEntropy]
    unfold phiEntropy
    rw [cubeExpect_noise]
    dsimp [u]
    ring
  change 2*theta^2+2*gamma*(cubeExpect (fun x => phi (u x))-phi r) +
      lam^2 * ∑ S : Finset (Fin n),
        (gamma-(gamma+1)^2/(gamma+S.card))*fourierCoeff u S^2 ≤ _ at hh
  rw [hi] at hh
  exact hh

end MostInformativeBit
