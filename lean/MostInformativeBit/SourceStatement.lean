import MostInformativeBit.InfluentialCoordinate
import MostInformativeBit.NoiseComplement

namespace MostInformativeBit

/-- The paper's literal bit-valued statement, with crossover probability p. -/
def SourceTheorem : Prop :=
  ∀ n (f : Cube n → Bool) (p : ℝ), 0 ≤ p → p ≤ 1/2 →
    GeneralCK.mutualInformation f p ≤ 1-GeneralCK.H p

theorem source_of_main (hm : MainTheorem) : SourceTheorem := by
  intro n f p hp0 hp1
  have hh := (information_le_phi_iff f (1-2*p)).mp
    (hm n f (1-2*p) (by linarith) (by linarith))
  simpa only [show (1-(1-2*p))/2 = p by ring] using hh

theorem main_of_source (hs : SourceTheorem) : MainTheorem := by
  intro n f r hr0 hr1
  exact (information_le_phi_iff f r).mpr
    (hs n f ((1-r)/2) (by linarith) (by linarith))

theorem source_iff_main : SourceTheorem ↔ MainTheorem :=
  ⟨main_of_source, source_of_main⟩

/-- Output complementation extends the manuscript's convention to all BSC
crossover probabilities, with precisely the upstream general statement. -/
theorem general_of_source (hs : SourceTheorem) : GeneralCK.GeneralCourtadeKumar := by
  intro n f p hp0 hp1
  by_cases hp : p ≤ 1/2
  · exact hs n f p hp0 hp
  · have hh := hs n f (1-p) (by linarith) (by linarith)
    simpa only [GeneralCK.mutualInformation_complement, GeneralCK.H_complement] using hh

/-- The half-range and full-range formulations are equivalent. -/
theorem source_iff_general : SourceTheorem ↔ GeneralCK.GeneralCourtadeKumar := by
  constructor
  · exact general_of_source
  · intro hg n f p hp0 hp1
    exact hg n f p hp0 (by linarith)

/-- Dictators attain the benchmark under the same actual BSC information definition. -/
theorem information_dictator {n : ℕ} (i : Fin n) (r : ℝ) :
    information (fun x : Cube n => x i) r = phi r := by
  have hs : signField (fun x : Cube n => x i) = character {i} := by
    funext x
    simp [signField, character]
  have hm : cubeExpect (character ({i} : Finset (Fin n))) = 0 := by
    simpa using character_orthogonality ({i} : Finset (Fin n)) ∅
  rw [information_eq_phiEntropy, hs, phiEntropy, cubeExpect_noise, hm, phi_zero, sub_zero]
  have he (x : Cube n) : phi (noise r (character {i}) x) = phi r := by
    rw [noise_character]
    simp only [Finset.card_singleton, pow_one, character, Finset.prod_singleton]
    cases hxi : x i <;> simp [cubeSign, phi, h_neg]
  simp_rw [he]
  exact cubeExpect_const _

theorem mutualInformation_dictator {n : ℕ} (i : Fin n) (p : ℝ) :
    GeneralCK.mutualInformation (fun x : Cube n => x i) p = 1-GeneralCK.H p := by
  have hh := information_dictator i (1-2*p)
  have hp : (1-(1-2*p))/2 = p := by ring
  unfold information phi h at hh
  rw [hp] at hh
  unfold GeneralCK.H
  have hL := GeneralCK.log_two_pos
  apply (mul_left_cancel₀ hL.ne')
  field_simp
  nlinarith only [hh]

end MostInformativeBit
