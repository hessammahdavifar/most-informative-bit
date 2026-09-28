import MostInformativeBit.TangentMinorant

namespace MostInformativeBit

noncomputable def lowBeta : ℝ :=
  (1/TangentMinorant.A (2/5)-1/TangentMinorant.A (2/3)) /
    (TangentMinorant.z (2/3)-TangentMinorant.z (2/5))

noncomputable def lowAlpha : ℝ :=
  1/TangentMinorant.A (2/5)+lowBeta*TangentMinorant.z (2/5)

noncomputable def lowCutoff : ℝ := Real.tanh (31/20)

noncomputable def lowCoefficient (r : ℝ) : ℝ := 1/(lowAlpha-lowBeta*r^2)

noncomputable def lowGap (r : ℝ) : ℝ :=
  (1-r)*(1+r-(49:ℝ)/64*r^2)-(lowAlpha-lowBeta*r^2)*h r

noncomputable def lowGapFirst (r : ℝ) : ℝ :=
  -2*(1+(49:ℝ)/64)*r+3*(49:ℝ)/64*r^2+2*lowBeta*r*h r+
    (lowAlpha-lowBeta*r^2)*Real.artanh r

noncomputable def lowGapSecond (r : ℝ) : ℝ :=
  -2*(1+(49:ℝ)/64)+6*(49:ℝ)/64*r+2*lowBeta*h r-
    4*lowBeta*r*Real.artanh r+(lowAlpha-lowBeta*r^2)/(1-r^2)

noncomputable def lowGapThird (r : ℝ) : ℝ :=
  6*(49:ℝ)/64-6*lowBeta*Real.artanh r-6*lowBeta*r/(1-r^2)+
    2*r*(lowAlpha-lowBeta*r^2)/(1-r^2)^2

/-- Explicit finite obligations from low.tex; no instance is assumed. -/
structure LowFixedFacts : Prop where
  alpha_lower : (53:ℝ)/40 < lowAlpha
  beta_lower : 0 < lowBeta
  beta_upper : lowBeta < 17/20
  cutoff_lower : (4:ℝ)/5 < lowCutoff
  cutoff_upper : lowCutoff < 1
  first_at_start : lowGapFirst (5/8) < -17/250
  second_at_start : lowGapSecond (5/8) < 7/30
  third_at_start : lowGapThird (5/8) < -1
  second_at_join : lowGapSecond (4/5) < -1/9
  second_at_end : lowGapSecond lowCutoff < -1/10
  value_at_end : (1:ℝ)/4000 < lowGap lowCutoff
  starting_slack : (1:ℝ)/500 <
    lowCoefficient (5/8)*(1-5/8)*(1+5/8-(49:ℝ)/64*(5/8)^2)+(5/8)^2/2-Real.log 2

end MostInformativeBit
