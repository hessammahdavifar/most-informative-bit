import MostInformativeBit.MiddleChannel
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Angular saving and decreasing losses at the canonical half-height join.
The angular estimate uses the proved arctangent brackets directly. -/
namespace MostInformativeBit.HighAngular
open Set Real ChannelProfiles ChannelBounds MiddleChannel

noncomputable def P : ℝ := Real.pi^2/4

lemma P_pos : 0 < P := by unfold P; positivity
lemma P_lt : P < 5/2 := by
  have hp := Real.pi_lt_d6
  have hp0 := Real.pi_pos
  unfold P
  nlinarith

lemma exp_seven_fourths : (40:ℝ)/7 < Real.exp (7/4) := by
  have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 7/4) 9
  norm_num [Finset.sum_range_succ, Nat.factorial] at hh
  linarith

lemma exp_neg_lt {v : ℝ} (hv : 7/4 ≤ v) : Real.exp (-v) < 7/40 := by
  rw [Real.exp_neg]
  apply (inv_lt_comm₀ (Real.exp_pos _) (by norm_num)).mpr
  norm_num
  exact exp_seven_fourths.trans_le (Real.exp_le_exp.mpr hv)

lemma c_exp (v : ℝ) :
    c v = (theta v)^2*(1+Real.exp (-v)^2)/(1-Real.exp (-v)^2) := by
  have hq : q v = Real.exp (-v)^2 := by
    unfold q
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  unfold c
  rw [tanh_eq_q, hq, div_div_eq_mul_div]

/-- A uniform lower bound for the angular deficit, from cubic arctangent bounds. -/
theorem angular_gap_lower {v : ℝ} (hv : 7/4 ≤ v) :
    (5*P/3)*Real.exp (-v) < P-c v := by
  let x := Real.exp (-v)
  have hx : 0 < x := Real.exp_pos _
  have hx1 : x < 7/40 := exp_neg_lt hv
  have hv0 : 0 ≤ v := by linarith
  have ha0 : 0 ≤ Real.arctan x := Real.arctan_nonneg.mpr hx.le
  have ha1 := arctan_le_self hx.le
  have ha2 := arctan_lower_cubic hx.le
  have ha3 : (Real.arctan x)^2 ≤ x^2 := pow_le_pow_left₀ ha0 ha1 2
  have hpi0 := Real.pi_pos
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  have hx3 : x^3 ≤ (7/40)*x^2 := by nlinarith [sq_nonneg x]
  have htheta : (theta v)^2 ≤ P-6*x+(9/2)*x^2 := by
    rw [theta_exp v hv0]
    change (Real.pi/2-2*Real.arctan x)^2 ≤ _
    have hp1 := mul_le_mul_of_nonneg_left ha2 (show 0 ≤ 2*Real.pi by positivity)
    have hp2 := mul_le_mul_of_nonneg_right hpi3.le hx.le
    have hp3 := mul_le_mul_of_nonneg_right hpi4.le (pow_nonneg hx.le 3)
    unfold P
    nlinarith
  have hxs : x^2 ≤ (7/40)^2 := pow_le_pow_left₀ hx.le hx1.le 2
  have hd : 0 < 1-x^2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right htheta (show 0 ≤ 1+x^2 by positivity)
  have hcoef : 2*P+(9/2)*(1+x^2) < 10 := by nlinarith [P_lt]
  have hbound : 6*x-10*x^2 ≤ P*(1-x^2)-(theta v)^2*(1+x^2) := by
    nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hcoef.le), pow_nonneg hx.le 3]
  have hlin : (17/4)*x < 6*x-10*x^2 := by nlinarith
  have hP : (5*P/3)*x < (17/4)*x := by nlinarith [mul_pos hx (sub_pos.mpr P_lt)]
  have hdrop : (5*P/3)*x*(1-x^2) ≤ (5*P/3)*x := by
    have := mul_nonneg (show 0 ≤ (5*P/3)*x by have := P_pos; positivity) (sq_nonneg x)
    nlinarith
  have hnum := hdrop.trans_lt (hP.trans (hlin.trans_le hbound))
  rw [c_exp]
  change (5*P/3)*x < P-(theta v)^2*(1+x^2)/(1-x^2)
  have hdiv : (theta v)^2*(1+x^2)/(1-x^2) < P-(5*P/3)*x := by
    apply (div_lt_iff₀ hd).mpr
    nlinarith
  linarith

lemma c_lower {v : ℝ} (hv : 0 < v) : P-2*Real.pi*Real.exp (-v) ≤ c v := by
  have hx : 0 ≤ Real.exp (-v) := (Real.exp_pos _).le
  have ha := arctan_le_self hx
  have hp := mul_le_mul_of_nonneg_left ha (show 0 ≤ 2*Real.pi by positivity)
  have htheta : P-2*Real.pi*Real.exp (-v) ≤ (theta v)^2 := by
    rw [theta_exp v hv.le]
    unfold P
    nlinarith [sq_nonneg (Real.arctan (Real.exp (-v)))]
  have hr : 0 < Real.tanh v := CenteredSupport.tanh_pos hv
  have hr1 : Real.tanh v ≤ 1 := (Real.tanh_lt_one v).le
  have hc : (theta v)^2 ≤ c v := by
    unfold c
    apply (le_div_iff₀ hr).mpr
    nlinarith [mul_nonneg (sq_nonneg (theta v)) (sub_nonneg.mpr hr1)]
  exact htheta.trans hc

/-- Exact angular saving used in the joining-height estimate. -/
theorem half_height_saving {ell : ℝ} (he : 7/2 ≤ ell) :
    (5*(Real.pi^2/4)/3)*Real.exp (-ell/2)-2*Real.pi*Real.exp (-ell) <
      c ell-c (ell/2) := by
  have hg := angular_gap_lower (v := ell/2) (by linarith)
  have hc := c_lower (v := ell) (by linarith)
  rw [show -(ell/2) = -ell/2 by ring] at hg
  unfold P at hg hc
  linarith

noncomputable def joiningLossOne (ell : ℝ) : ℝ :=
  (7*ell/6+5/4+8/Real.pi)*Real.exp (-ell/2)
noncomputable def joiningLossTwo (ell : ℝ) : ℝ :=
  ((ell/2-3/4)*(2*ell+1)/(2*Real.log 2))*Real.exp (-3*ell/2)

lemma joiningLossOne_hasDerivAt (ell : ℝ) :
    HasDerivAt joiningLossOne
      ((7/6-(7*ell/6+5/4+8/Real.pi)/2)*Real.exp (-ell/2)) ell := by
  unfold joiningLossOne
  convert (((((hasDerivAt_id ell).const_mul 7).div_const 6).add_const (5/4)).add_const
    (8/Real.pi)).mul (((hasDerivAt_id ell).neg.div_const 2).exp) using 1 <;> try rfl
  all_goals dsimp; ring

lemma joiningLossTwo_hasDerivAt (ell : ℝ) :
    HasDerivAt joiningLossTwo
      (((2*ell-1)-3/2*(ell/2-3/4)*(2*ell+1))/(2*Real.log 2)*
        Real.exp (-3*ell/2)) ell := by
  unfold joiningLossTwo
  convert (((((hasDerivAt_id ell).div_const 2).sub_const (3/4)).mul
    (((hasDerivAt_id ell).const_mul 2).add_const 1)).div_const (2*Real.log 2)).mul
    ((((hasDerivAt_id ell).const_mul (-3)).div_const 2).exp) using 1 <;> try rfl
  all_goals dsimp; ring

lemma joining_loss_one_antitone : AntitoneOn joiningLossOne (Ici (7/2)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact fun ell _ => (joiningLossOne_hasDerivAt ell).continuousAt.continuousWithinAt
  · exact fun ell _ => (joiningLossOne_hasDerivAt ell).differentiableAt.differentiableWithinAt
  · intro ell hell
    rw [(joiningLossOne_hasDerivAt ell).deriv]
    apply mul_nonpos_of_nonpos_of_nonneg _ (Real.exp_pos _).le
    have hel := interior_subset hell
    have hp : 0 < 8/Real.pi := by positivity
    simp only [mem_Ici] at hel
    linarith

lemma joining_loss_two_antitone : AntitoneOn joiningLossTwo (Ici (7/2)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact fun ell _ => (joiningLossTwo_hasDerivAt ell).continuousAt.continuousWithinAt
  · exact fun ell _ => (joiningLossTwo_hasDerivAt ell).differentiableAt.differentiableWithinAt
  · intro ell hell
    rw [(joiningLossTwo_hasDerivAt ell).deriv]
    apply mul_nonpos_of_nonpos_of_nonneg _ (Real.exp_pos _).le
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    have hel := interior_subset hell
    simp only [mem_Ici] at hel
    nlinarith [sq_nonneg (ell-7/2)]

/-- First decreasing joining loss, bounded at the endpoint 7/2. -/
theorem joining_loss_one {ell : ℝ} (he : 7/2 ≤ ell) :
    (7*ell/6+5/4+8/Real.pi)*Real.exp (-ell/2) < 7/5 := by
  have hmono := joining_loss_one_antitone (a := 7/2) (b := ell) (by simp) he he
  change joiningLossOne ell < 7/5
  apply hmono.trans_lt
  have hex := exp_neg_lt (v := 7/4) le_rfl
  have hpi : 8/Real.pi < 8/3 := by
    exact div_lt_div_of_pos_left (by norm_num) (by norm_num) Real.pi_gt_three
  unfold joiningLossOne
  norm_num only
  have he0 := Real.exp_pos (-(7/4:ℝ))
  nlinarith

/-- Second decreasing joining loss, bounded at the endpoint 7/2. -/
theorem joining_loss_two {ell : ℝ} (he : 7/2 ≤ ell) :
    ((ell/2-3/4)*(2*ell+1)/(2*Real.log 2))*Real.exp (-3*ell/2) < 1/25 := by
  have hmono := joining_loss_two_antitone (a := 7/2) (b := ell) (by simp) he he
  change joiningLossTwo ell < 1/25
  apply hmono.trans_lt
  have hex := exp_neg_lt (v := 7/4) le_rfl
  have he0 := Real.exp_pos (-(7/4:ℝ))
  have hp := pow_lt_pow_left₀ hex he0.le (by norm_num : (3:ℕ) ≠ 0)
  have hL : (2/3:ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hcoef : 8/(2*Real.log 2) < 6 := by
    apply (div_lt_iff₀ (by positivity : 0 < 2*Real.log 2)).mpr
    linarith
  have hexid : Real.exp (-3*(7/2:ℝ)/2) = Real.exp (-(7/4:ℝ))^3 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  unfold joiningLossTwo
  rw [hexid]
  norm_num only
  have hp0 : 0 < Real.exp (-(7/4:ℝ))^3 := by positivity
  have hprod := mul_lt_mul_of_pos_right hcoef hp0
  norm_num at hp
  nlinarith

lemma r_tail_lower {ell : ℝ} (he : 7/2 ≤ ell) : 99/100 < r ell := by
  have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 7/2) 13
  norm_num [Finset.sum_range_succ, Nat.factorial] at hh
  have h33 : 33 < Real.exp ell := by
    have := Real.exp_le_exp.mpr he
    linarith
  rw [r_exp]
  have ht : 2/(Real.exp ell^2+1) < (1:ℝ)/100 := by
    apply (div_lt_div_iff₀ (by positivity : 0 < Real.exp ell^2+1) (by norm_num : (0:ℝ)<100)).mpr
    nlinarith [sq_nonneg (Real.exp ell-33)]
  linarith

/-- The explicit normalized joining reserve after the three spectral losses. -/
theorem joining_reserve {ell : ℝ} (he : 7/2 ≤ ell) :
    21/100 < 5*r ell/3 -
      (7*ell/6+5/4+8/Real.pi)*Real.exp (-ell/2) -
      ((ell/2-3/4)*(2*ell+1)/(2*Real.log 2))*Real.exp (-3*ell/2) := by
  have h₁ := joining_loss_one he
  have h₂ := joining_loss_two he
  have hr := r_tail_lower he
  linarith

end MostInformativeBit.HighAngular
