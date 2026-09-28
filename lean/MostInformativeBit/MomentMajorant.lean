import Mathlib.Tactic

/-! Exact polynomial parts of the singleton-energy argument in fourier-cap.tex.
The pointwise majorant is proved by factorization, replacing only the Hermite
interpolation remainder argument. The expectation/moment identities are separate.
-/
namespace MostInformativeBit

noncomputable def momentNumerator (y : ℝ) : ℝ :=
  637696*y^5 - 17928800*y^4 + 191446315*y^3 - 1008169920*y^2 +
  3660186285*y + 1260006516

noncomputable def momentMajorant (y : ℝ) : ℝ := momentNumerator y / 4042912500

theorem moment_majorant_factorization (z : ℝ) :
    momentNumerator (z^2) - 4042912500*z =
      (z-3/4)^2*(z-2)^2*(z-3)^2 *
        (62222544 + 69981024*z + 32887600*z^2 + 7333504*z^3 + 637696*z^4) := by
  unfold momentNumerator
  ring

theorem moment_majorant_nonneg {z : ℝ} (hz : 0 ≤ z) : z ≤ momentMajorant (z^2) := by
  have hf : 0 ≤ (z-3/4)^2*(z-2)^2*(z-3)^2 *
      (62222544 + 69981024*z + 32887600*z^2 + 7333504*z^3 + 637696*z^4) := by
    positivity
  rw [← moment_majorant_factorization] at hf
  unfold momentMajorant
  linarith

/-- The paper's pointwise majorant, including all real signs and zero. -/
theorem abs_le_momentMajorant (z : ℝ) : |z| ≤ momentMajorant (z^2) := by
  have hh := moment_majorant_nonneg (abs_nonneg z)
  simpa [sq_abs] using hh

noncomputable def momentBound (t : ℝ) : ℝ :=
  3487476486 + 77364454*t + 650389376*t^2 - 9583071744/5*t^3

theorem momentBound_increasing_to_endpoint {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1/5) :
    momentBound t ≤ momentBound (1/5) := by
  have hs : 0 ≤ t*(1/5-t) := mul_nonneg ht0 (by linarith)
  have hu : 0 ≤ 1/5-t := by linarith
  have hb : 0 ≤ 9583071744/5*t*(1/5-t) +
      2906409088/25*(1/5-t) + 13440810318/125 := by
    positivity
  have hp := mul_nonneg (show 0 ≤ 1/5-t by linarith) hb
  have he : momentBound (1/5) - momentBound t =
      (1/5-t) * (9583071744/5*t*(1/5-t) +
        2906409088/25*(1/5-t) + 13440810318/125) := by
    unfold momentBound
    ring
  linarith only [hp, he]

/-- Strict margin in the final arithmetic of the sign-sum argument. -/
theorem momentBound_lt_seven_eighths {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1/5) :
    momentBound t / 4042912500 < (7:ℝ)/8 := by
  have hh := momentBound_increasing_to_endpoint ht0 ht1
  have he : momentBound (1/5) / 4042912500 < (7:ℝ)/8 := by
    norm_num [momentBound]
  exact lt_of_le_of_lt (div_le_div_of_nonneg_right hh (by norm_num)) he

/-- Exact moment expression in the manuscript after the sign-sum expansion. -/
noncomputable def momentExpression (t s6 s8 s10 : ℝ) : ℝ :=
  3487476486 - 214438410*t + 1507452800*t^2 +
    (1459014320-4285317120*t)*s6 - 2928765440*s8 + 5060755456*s10

/-- The moment constraints imply the scalar bound; expansion of the moments
themselves is a separate combinatorial obligation. -/
theorem momentExpression_le_bound {t s6 s8 s10 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1/5)
    (h6 : s6 ≤ t/5) (h8 : t^3 ≤ s8) (h10 : s10 ≤ s8/5) :
    momentExpression t s6 s8 s10 ≤ momentBound t := by
  have hc : 0 ≤ 1459014320-4285317120*t := by linarith
  have hh6 := mul_le_mul_of_nonneg_left h6 hc
  unfold momentExpression momentBound
  nlinarith

theorem momentExpression_lt_seven_eighths {t s6 s8 s10 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1/5)
    (h6 : s6 ≤ t/5) (h8 : t^3 ≤ s8) (h10 : s10 ≤ s8/5) :
    momentExpression t s6 s8 s10 / 4042912500 < (7:ℝ)/8 := by
  exact lt_of_le_of_lt
    (div_le_div_of_nonneg_right (momentExpression_le_bound ht0 ht1 h6 h8 h10)
      (by norm_num)) (momentBound_lt_seven_eighths ht0 ht1)

end MostInformativeBit
