import MostInformativeBit.HighRegime
import MostInformativeBit.SourceStatement

namespace MostInformativeBit

/-- Courtade–Kumar for every dimension and every Boolean summary, in natural units. -/
theorem courtade_kumar : MainTheorem :=
  main_of_high_action_growth high_action_growth_holds

/-- Courtade–Kumar on the full crossover range, using the exact general
proposition from the upstream statement definitions. -/
theorem general_courtade_kumar : GeneralCK.GeneralCourtadeKumar :=
  general_of_source (source_of_main courtade_kumar)

/-- I(f(X);Y) <= 1-H₂(p), in bits, for every crossover probability in [0,1]. -/
theorem courtade_kumar_bits {n : ℕ} (f : Cube n → Bool) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    GeneralCK.mutualInformation f p ≤ 1-GeneralCK.H p :=
  general_courtade_kumar n f p hp0 hp1

theorem source_theorem : SourceTheorem := source_of_main courtade_kumar

end MostInformativeBit
