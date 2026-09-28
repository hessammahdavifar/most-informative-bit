import MostInformativeBit.AngularResolvent
import MostInformativeBit.CoordinateDeficit
import MostInformativeBit.GrowthBudget
import MostInformativeBit.EntropyBounds
import MostInformativeBit.LowRegime

namespace MostInformativeBit
open scoped BigOperators

theorem resolvent_weight_identity {n : ℕ} (u : Cube n → ℝ) {lam alpha : ℝ}
    (hl : 0 < lam) (ha : 0 < alpha) :
    lam^2*(∑ S : Finset (Fin n),
      (lam*alpha-(lam*alpha+1)^2/(lam*alpha+S.card))*fourierCoeff u S^2) =
    (lam+1/alpha)^2*(∑ S : Finset (Fin n), if S = ∅ then 0 else
      degWeight (lam*alpha) S.card * fourierCoeff u S^2) -
      lam^2*(2+1/(lam*alpha))*cubeExpect (fun x => u x^2) := by
  rw [parseval]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S _
  have hid := resolvent_multiplier_identity ha.ne' hl.ne'
    (show lam*alpha+(S.card:ℝ) ≠ 0 by positivity)
  by_cases hs : S = ∅
  · subst S
    simp only [Finset.card_empty, Nat.cast_zero, if_true, mul_zero, zero_sub,
      degWeight, mul_zero, zero_div] at *
    nlinarith
  · simp only [hs, if_false]
    unfold degWeight
    nlinarith

/-- The manuscript's spectral baseline, with both coordinate-deficit estimates
and the scalar entropy bounds discharged. Only its two stated channel sign
conditions and the choice of reference degree remain as hypotheses. -/
theorem spectral_baseline {n : ℕ} {f : Cube n → Bool} (hf : Monotone f)
    {ell D : ℝ} (hell : 31/20 ≤ ell) (hD : 2 ≤ D)
    (hC :
      let r := Real.tanh ell
      let lam := Real.arcsin r/r
      let alpha := (Real.arcsin r+Real.sinh ell)/ell
      let gamma := lam*alpha
      0 ≤ (lam+1/alpha)^2*degWeight gamma D-lam^2*(2+1/gamma))
    (hmean :
      let r := Real.tanh ell
      let lam := Real.arcsin r/r
      let alpha := (Real.arcsin r+Real.sinh ell)/ell
      let gamma := lam*alpha
      let b := lam^2*(2+1/gamma)
      let C := (lam+1/alpha)^2*degWeight gamma D-b
      0 ≤ gamma-b+C*(1/(2*Real.log 2)-1)) :
    let r := Real.tanh ell
    let u := noise r (signField f)
    let theta := Real.arcsin r
    let lam := theta/r
    let alpha := (theta+Real.sinh ell)/ell
    let gamma := lam*alpha
    let p := (lam+1/alpha)^2
    let b := lam^2*(2+1/gamma)
    let C := p*degWeight gamma D-b
    let B := 2*theta^2+C*phi r/Real.log 2
    let k := 2*gamma+C/Real.log 2
    B-p*(∑ i, deficitBound gamma D r (pivotalMean i f))+k*gap f r ≤
      cubeExpect (fun x => Real.arcsin (u x)*
        cubeLaplacian (fun y => Real.arcsin (u y)) x) := by
  intro r u theta lam alpha gamma p b C B k
  have he : 0 < ell := by linarith
  have hr : 0 < r := CenteredSupport.tanh_pos he
  have ht : 0 < theta := Real.arcsin_pos.mpr hr
  have hl : 0 < lam := div_pos ht hr
  have ha : 0 < alpha := div_pos (add_pos ht (Real.sinh_pos_iff.mpr he)) he
  have hg : 0 < gamma := mul_pos hl ha
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  change 0 ≤ C at hC
  change 0 ≤ gamma-b+C*(1/(2*Real.log 2)-1) at hmean
  have hp : 0 ≤ p := sq_nonneg _
  have hk : 0 < k := add_pos_of_pos_of_nonneg (by positivity)
    (div_nonneg hC hL.le)
  have ha0 := boolean_angular_resolvent f hell
  change 2*theta^2+2*gamma*(phi (cubeExpect (signField f))+gap f r)+
      lam^2*(∑ S : Finset (Fin n), (lam*alpha-(lam*alpha+1)^2/(lam*alpha+S.card))*
        fourierCoeff (noise r (signField f)) S^2) ≤ _ at ha0
  rw [resolvent_weight_identity (noise r (signField f)) hl ha] at ha0
  have hspec := spectral_deficit hg hD hr (Real.tanh_lt_one ell).le hf
  rw [cubeExpect_noise] at hspec
  have hspecp := mul_le_mul_of_nonneg_left hspec hp
  have hu : ∀ x, u x ∈ Set.Icc (-1) 1 :=
    noise_mem_Icc (by linarith) (Real.tanh_lt_one ell).le (signField_mem_Icc f)
  have heup := cubeExpect_phi_upper u hu
  have heq : cubeExpect (fun x => phi (u x)) =
      phi r+phi (cubeExpect (signField f))+gap f r := by
    rw [gap, information_eq_phiEntropy]
    unfold phiEntropy
    rw [cubeExpect_noise]
    dsimp [u]
    ring
  rw [heq] at heup
  have hcredit := mul_le_mul_of_nonneg_left heup (div_nonneg hC hL.le)
  have hcredit' : C/Real.log 2*(phi r+phi (cubeExpect (signField f))+gap f r) ≤
      C*cubeExpect (fun x => u x^2) := by
    have hid : C/Real.log 2*(Real.log 2*cubeExpect (fun x => u x^2)) =
        C*cubeExpect (fun x => u x^2) := by field_simp
    rwa [hid] at hcredit
  have hm := phi_quadratic_lower (abs_le.mpr (cubeExpect_mem_Icc (signField_mem_Icc f)))
  have hmp := mul_le_mul_of_nonneg_left hm hk.le
  have hmc := mul_nonneg hmean (sq_nonneg (cubeExpect (signField f)))
  have hkmean : 0 ≤ k*phi (cubeExpect (signField f))-
      (C+b)*cubeExpect (signField f)^2 := by
    have hid : k/2-(C+b) = gamma-b+C*(1/(2*Real.log 2)-1) := by
      dsimp [k]
      field_simp
      ring
    rw [← hid] at hmc
    nlinarith only [hmp, hmc]
  change 2*theta^2+2*gamma*(phi (cubeExpect (signField f))+gap f r)+
      (p*(∑ S : Finset (Fin n), if S = ∅ then 0 else
        degWeight gamma S.card * fourierCoeff u S^2)-
        b*cubeExpect (fun x => u x^2)) ≤
    cubeExpect (fun x => Real.arcsin (u x)*
      cubeLaplacian (fun y => Real.arcsin (u y)) x) at ha0
  change p*(degWeight gamma D*(cubeExpect (fun x => u x^2)-
      cubeExpect (signField f)^2)-(∑ i, deficitBound gamma D r (pivotalMean i f))) ≤
      p*(∑ S : Finset (Fin n), if S = ∅ then 0 else
        degWeight gamma S.card*fourierCoeff u S^2) at hspecp
  dsimp [B, k, C]
  dsimp [k, C] at hcredit' hkmean
  simp only [div_eq_mul_inv] at hcredit' hkmean ⊢
  nlinarith only [ha0, hspecp, hcredit', hkmean]

end MostInformativeBit
