import MostInformativeBit.LowCertificates
import MostInformativeBit.LowGapCalculus

namespace MostInformativeBit

/-- The exact low-correlation scalar minorant, with both contact checks discharged. -/
theorem low_minorant {r s : ℝ} (hr0 : 5/8 ≤ r) (hr1 : r ≤ lowCutoff)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 < lowAlpha-lowBeta*r^2 ∧
      lowCoefficient r*(1-s)*(1+s-r^2) ≤ h s := by
  have hp : 0 ≤ r := by linarith
  have hc : 0 ≤ lowCutoff := le_trans hp hr1
  have hl : TangentMinorant.z (2/5) ≤ r^2 := by
    have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5/8) hr0 2
    linarith [low_z0_lt_start_sq]
  have hu : r^2 ≤ TangentMinorant.z (2/3) :=
    le_trans (pow_le_pow_left₀ hp hr1 2) low_end_sq_lt_z1.le
  have hz : TangentMinorant.z (2/5) < TangentMinorant.z (2/3) := by
    have hsq := pow_le_pow_left₀ hp hr1 2
    linarith [low_z0_lt_start_sq, low_end_sq_lt_z1]
  exact TangentMinorant.weighted_minorant (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hz hl hu hs0 hs1

theorem low_coefficient_pos {r : ℝ} (hr0 : 5/8 ≤ r) (hr1 : r ≤ lowCutoff) :
    0 < lowCoefficient r := by
  exact one_div_pos.mpr (low_minorant hr0 hr1 (s := 0) le_rfl zero_le_one).1

theorem low_gap_positive {r : ℝ} (hr0 : 5/8 ≤ r) (hr1 : r ≤ lowCutoff) :
    0 < lowGap r :=
  LowGapCalculus.lowGap_pos low_fixed_facts hr0 hr1

theorem low_mean_coefficient_nonneg {r : ℝ} (hr0 : 5/8 ≤ r) (hr1 : r ≤ 1) :
    0 ≤ 1/2-lowCoefficient r*(1-2*r^2+r^3) :=
  LowGapCalculus.mean_coefficient_nonneg low_fixed_facts hr0 hr1

theorem low_scalar_bound {r : ℝ} (hr0 : 5/8 ≤ r) (hr1 : r ≤ lowCutoff) :
    h r < lowCoefficient r*(1-r)*(1+r-(49:ℝ)/64*r^2) := by
  have hp := (low_minorant hr0 hr1 (s := 0) le_rfl zero_le_one).1
  have hg := low_gap_positive hr0 hr1
  unfold lowGap at hg
  unfold lowCoefficient
  apply (mul_lt_mul_iff_left₀ hp).mp
  field_simp
  nlinarith

end MostInformativeBit
