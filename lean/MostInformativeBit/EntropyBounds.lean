import MostInformativeBit.EntropyTensorization

namespace MostInformativeBit

theorem cubeExpect_one_sign (g : ℝ → ℝ) :
    cubeExpect (fun x : Cube 1 => g (cubeSign (x 0))) = (g (-1)+g 1)/2 := by
  rw [cubeExpect_succ]
  norm_num [cubeSign, cubeExpect_const]

/-- The scalar entropy upper bound follows from the proved sharp contraction
on the one-dimensional sign character. -/
theorem phi_quadratic_upper {t : ℝ} (ht : t ∈ Set.Icc (-1) 1) :
    phi t ≤ Real.log 2*t^2 := by
  let v : Cube 1 → ℝ := fun x => cubeSign (x 0)
  have hv : ∀ x, v x ∈ Set.Icc (-1) 1 := by
    intro x
    dsimp [v]
    cases x 0 <;> norm_num [cubeSign]
  have hnoise : noise t v = fun x => t*v x := by
    have he : v = character ({0} : Finset (Fin 1)) := by
      funext x
      simp [v, character]
    rw [he]
    funext x
    simp only [noise_character, Finset.card_singleton, pow_one]
  have heven (x : ℝ) : phi (-x) = phi x := by
    unfold phi h
    rw [show (1- -x)/2 = 1-(1-x)/2 by ring, Real.binEntropy_one_sub]
  have hmean : cubeExpect v = 0 := by
    have hh := cubeExpect_one_sign id
    norm_num at hh
    exact hh
  have hq : phiEntropy v = Real.log 2 := by
    unfold phiEntropy
    rw [hmean, phi_zero]
    have hh := cubeExpect_one_sign phi
    rw [show phi (-1) = Real.log 2 by norm_num [phi, h],
      show phi 1 = Real.log 2 by norm_num [phi, h]] at hh
    dsimp [v]
    linarith
  have hn : phiEntropy (noise t v) = phi t := by
    rw [hnoise]
    unfold phiEntropy
    rw [cubeExpect_mul, hmean, mul_zero, phi_zero, sub_zero]
    have hh := cubeExpect_one_sign (fun z => phi (t*z))
    norm_num only [mul_neg_one, mul_one] at hh
    rw [heven] at hh
    change cubeExpect (fun x : Cube 1 => phi (t*cubeSign (x 0))) = _
    linarith
  have hc := phiEntropyContraction_holds ht.1 ht.2 v hv
  rw [hn, hq] at hc
  nlinarith

theorem cubeExpect_phi_upper {n : ℕ} (u : Cube n → ℝ)
    (hu : ∀ x, u x ∈ Set.Icc (-1) 1) :
    cubeExpect (fun x => phi (u x)) ≤ Real.log 2*cubeExpect (fun x => u x^2) := by
  have hh := cubeExpect_mono (fun x => phi_quadratic_upper (hu x))
  rwa [cubeExpect_mul] at hh

end MostInformativeBit
