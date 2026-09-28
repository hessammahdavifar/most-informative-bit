import MostInformativeBit.LowDefinitions
import MostInformativeBit.IntervalBounds

namespace MostInformativeBit
open MeanCorrection TangentMinorant

theorem lowCutoff_exp :
    lowCutoff = (Real.exp (31/10)-1)/(Real.exp (31/10)+1) := by
  have he : Real.exp ((31:ℝ)/10) = Real.exp (31/20)^2 := by
    rw [show (31:ℝ)/10 = 31/20+31/20 by ring, Real.exp_add]
    ring
  have hp := Real.exp_pos ((31:ℝ)/20)
  unfold lowCutoff
  rw [Real.tanh_eq, Real.exp_neg, he]
  field_simp

theorem h_log_formula {x : ℝ} (h0 : -1 < x) (h1 : x < 1) :
    h x = Real.log 2-Real.log (1+x)+(1-x)*Real.artanh x := by
  rw [h_eq, phi_eq_dv h0 h1, artanh_eq_dv1 h0 h1]
  unfold dv dv1
  ring

end MostInformativeBit
