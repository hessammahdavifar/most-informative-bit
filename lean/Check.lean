import MostInformativeBit

open scoped BigOperators

-- Final unconditional theorem and its literal formulation in bits.
#print MostInformativeBit.courtade_kumar_bits
#print MostInformativeBit.general_courtade_kumar
#print GeneralCK.GeneralCourtadeKumar
#print axioms MostInformativeBit.general_courtade_kumar
#print axioms GeneralCK.mutualInformation_complement
#print axioms MostInformativeBit.general_of_source
#print axioms MostInformativeBit.source_iff_general
#print axioms MostInformativeBit.courtade_kumar
#print axioms MostInformativeBit.courtade_kumar_bits
#print axioms MostInformativeBit.source_theorem
#print axioms MostInformativeBit.high_action_growth

-- Accepted unconditional components.
#print axioms MostInformativeBit.ck_low
#print axioms MostInformativeBit.middle_action_growth
#print axioms MostInformativeBit.HighLocal.local_cutoff
#print axioms MostInformativeBit.OriginalYield.original_yield_no_interior_max
#print axioms MostInformativeBit.HighAngular.joining_reserve
#print axioms MostInformativeBit.monotoneReduction
#print axioms MostInformativeBit.EdgeBudget.edge_budget
#print axioms MostInformativeBit.spectral_baseline
#print axioms MostInformativeBit.information_dictator
#print axioms MostInformativeBit.mutualInformation_dictator
#print axioms MostInformativeBit.source_iff_main

-- These are explicitly conditional reductions, not the final CK theorem.
#print MostInformativeBit.HighActionGrowth
#print axioms MostInformativeBit.action_growth_of_coordinate_cost
#check MostInformativeBit.action_growth_of_coordinate_cost
#print axioms MostInformativeBit.main_of_high_action_growth
#check MostInformativeBit.main_of_high_action_growth

-- The exact full-range proposition used by the upstream formalization.
example : GeneralCK.GeneralCourtadeKumar := MostInformativeBit.general_courtade_kumar

-- Expanded finite-distribution statement on the entire probability interval.
example {n : ℕ} (f : GeneralCK.Cube n → Bool) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    GeneralCK.entropy (fun b => ∑ y, GeneralCK.jointMass f p b y) +
      GeneralCK.entropy (fun y => ∑ b, GeneralCK.jointMass f p b y) -
      GeneralCK.entropy (fun z : Bool × GeneralCK.Cube n =>
        GeneralCK.jointMass f p z.1 z.2) ≤
      1-Real.binEntropy p/Real.log 2 :=
  MostInformativeBit.courtade_kumar_bits f hp0 hp1
