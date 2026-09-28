import MostInformativeBit.AngularResolvent
import MostInformativeBit.PivotalEntropy

namespace MostInformativeBit
open scoped BigOperators

theorem resolvent_pivotal_identity {n : ℕ} {gamma r : ℝ}
    (hg : 0 < gamma) (hr : 0 < r) (f : Cube n → Bool) :
    (∑ S : Finset (Fin n),
      (gamma-(gamma+1)^2/(gamma+S.card))*
        fourierCoeff (noise r (signField f)) S^2) =
      gamma*r^2*noisyVarRatio r f -
        (2+1/gamma)*cubeExpect (signField f)^2 -
        (gamma+1)*r^2*pivotalTotal gamma r f := by
  have he : (∑ S : Finset (Fin n),
      if S = ∅ then (2+1/gamma)*fourierCoeff (signField f) S^2 else 0) =
      (2+1/gamma)*cubeExpect (signField f)^2 := by simp
  rw [noisyVarRatio_eq hr, pivotalTotal_eq hg hr, ← he]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S _
  rw [fourierCoeff_noise, mul_pow]
  by_cases hs : S = ∅
  · subst S
    simp
    field_simp
    ring
  · simp only [hs, if_false]
    have hc : 1 ≤ S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
    have hden : 0 < gamma+(S.card:ℝ) := by positivity
    rw [← pow_mul, Nat.mul_comm S.card 2,
      show 2*S.card = 2*(S.card-1)+2 by omega, pow_add]
    field_simp
    ring

/-- The source's pivotal angular baseline, now for the actual cube field and actual
integrated pivotal weights. The only hypotheses are the manuscript's channel
threshold and monotonicity of the Boolean rule. -/
theorem angular_pivotal_baseline {n : ℕ} {f : Cube n → Bool} (hf : Monotone f)
    {ell : ℝ} (hell : 31/20 ≤ ell) :
    let r := Real.tanh ell
    let u := noise r (signField f)
    let m := cubeExpect (signField f)
    let theta := Real.arcsin r
    let lam := theta/r
    let alpha := (theta+Real.sinh ell)/ell
    let gamma := lam*alpha
    let eta := theta^2*gamma/(gamma+1)
    let M := 2*gamma*phi m-(lam^2*(2-r^2)+lam/alpha)*m^2
    theta^2*(1+meanDefect f-pivotalTotal gamma r f) +
      eta/2*(∑ i, pivotalAverage gamma r i f*
        Real.log (pivotalAverage gamma r i f/pivotalMean i f^2)) +
      M+2*gamma*gap f r ≤
    cubeExpect (fun x => Real.arcsin (u x)*
      cubeLaplacian (fun y => Real.arcsin (u y)) x) := by
  intro r u m theta lam alpha gamma eta M
  have he : 0 < ell := by linarith
  have hr : 0 < r := CenteredSupport.tanh_pos he
  have ht : 0 < theta := Real.arcsin_pos.mpr hr
  have hl : 0 < lam := div_pos ht hr
  have ha : 0 < alpha := div_pos
    (add_pos ht (Real.sinh_pos_iff.mpr he)) he
  have hg : 0 < gamma := mul_pos hl ha
  have hgp : 0 < gamma+1 := by positivity
  have htheta : lam^2*r^2 = theta^2 := by dsimp [lam]; field_simp
  have hga : lam^2/gamma = lam/alpha := by dsimp [gamma]; field_simp
  have hvar : meanDefect f = 1-m^2 := rfl
  have had := boolean_angular_resolvent f hell
  change 2*theta^2+2*gamma*(phi m+gap f r)+
      lam^2*(∑ S : Finset (Fin n), (gamma-(gamma+1)^2/(gamma+S.card))*
        fourierCoeff (noise r (signField f)) S^2) ≤ _ at had
  rw [resolvent_pivotal_identity hg hr f] at had
  have hid :
      2*theta^2+2*gamma*(phi m+gap f r)+
        lam^2*(gamma*r^2*noisyVarRatio r f -
          (2+1/gamma)*m^2-(gamma+1)*r^2*pivotalTotal gamma r f) =
      theta^2*(1+meanDefect f-pivotalTotal gamma r f)+M+2*gamma*gap f r+
        theta^2*gamma*(noisyVarRatio r f-pivotalTotal gamma r f) := by
    rw [hvar]
    dsimp [M, gamma, lam]
    field_simp
    ring
  rw [hid] at had
  have hp := pivotal_entropy hg hr (Real.tanh_lt_one ell).le hf
  have hmult := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ theta^2*gamma/(gamma+1) by positivity)
  have heq : theta^2*gamma/(gamma+1)*
      ((gamma+1)*(noisyVarRatio r f-pivotalTotal gamma r f)) =
      theta^2*gamma*(noisyVarRatio r f-pivotalTotal gamma r f) := by field_simp
  rw [heq] at hmult
  change eta*(_/2) ≤ _ at hmult
  linarith

end MostInformativeBit
