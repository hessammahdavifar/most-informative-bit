import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace MostInformativeBit
open scoped BigOperators
open Real

/-- Finite log-sum inequality, allowing zero entries in the first vector. -/
theorem finite_log_sum {ι : Type*} (s : Finset ι) (z b : ι → ℝ)
    (hz : ∀ i ∈ s, 0 ≤ z i) (hb : ∀ i ∈ s, 0 < b i)
    (hZ : 0 < ∑ i ∈ s, z i) (hB : 0 < ∑ i ∈ s, b i) :
    (∑ i ∈ s, z i)*log ((∑ i ∈ s, z i)/(∑ i ∈ s, b i)) ≤
      ∑ i ∈ s, z i*log (z i/b i) := by
  let c := (∑ i ∈ s, z i)/(∑ i ∈ s, b i)
  have hc : 0 < c := div_pos hZ hB
  have hpt (i) (hi : i ∈ s) :
      z i*log c+z i-c*b i ≤ z i*log (z i/b i) := by
    rcases (hz i hi).eq_or_lt with he | hp
    · rw [← he]
      simp only [zero_mul, zero_add, sub_nonpos]
      exact mul_nonneg hc.le (hb i hi).le
    · have hh := Real.log_le_sub_one_of_pos (div_pos (mul_pos hc (hb i hi)) hp)
      rw [Real.log_div (mul_pos hc (hb i hi)).ne' hp.ne',
        Real.log_mul hc.ne' (hb i hi).ne'] at hh
      have hm := mul_le_mul_of_nonneg_left hh hp.le
      have he : z i*(c*b i/z i-1) = c*b i-z i := by field_simp
      rw [Real.log_div hp.ne' (hb i hi).ne']
      nlinarith
  have hh := Finset.sum_le_sum hpt
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum] at hh
  have he : c*(∑ i ∈ s, b i) = ∑ i ∈ s, z i := by dsimp [c]; field_simp
  rw [he] at hh
  dsimp [c] at hh
  linarith

/-- Changing a positive reference mass to a larger upper bound weakens log-sum. -/
theorem log_sum_upper_reference {Z B V t : ℝ}
    (hZ : 0 < Z) (hB : 0 < B) (hV : 0 < V)
    (hb : B ≤ V*exp (-t)) :
    Z*log (Z/V)+Z*t ≤ Z*log (Z/B) := by
  have hh := Real.log_le_log hB hb
  rw [Real.log_mul hV.ne' (Real.exp_pos _).ne', Real.log_exp] at hh
  rw [Real.log_div hZ.ne' hV.ne', Real.log_div hZ.ne' hB.ne']
  nlinarith

/-- Exact entropy compensation used to close the middle-regime edge budget. -/
theorem pivotal_log_compensation {ι : Type*} (s : Finset ι)
    (z a H : ι → ℝ) {r eta V Htop : ℝ}
    (hr : 0 ≤ r) (he : 0 < eta) (hV : 0 < V)
    (ha : ∀ i ∈ s, 0 < a i) (hz : ∀ i ∈ s, 0 ≤ z i)
    (hza : ∀ i ∈ s, z i ≤ a i) (hH : ∀ i ∈ s, 0 ≤ H i)
    (hZ : 0 < ∑ i ∈ s, z i)
    (hbudget : (∑ i ∈ s, a i^2*exp (-(2*r/eta)*H i)) ≤
      V*exp (-(2*r/eta)*Htop)) :
    eta/2*(∑ i ∈ s, z i*log (z i/a i^2))+
      r*(∑ i ∈ s, a i*H i) ≥
    eta/2*((∑ i ∈ s, z i)*log ((∑ i ∈ s, z i)/V))+
      r*(∑ i ∈ s, z i)*Htop := by
  let beta := 2*r/eta
  let b (i : ι) := a i^2*exp (-beta*H i)
  have hb (i) (hi : i ∈ s) : 0 < b i := by
    have hi' := ha i hi
    dsimp [b]
    positivity
  have hne : s.Nonempty := by
    by_contra hn
    have hs := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [hs] at hZ
  have hB : 0 < ∑ i ∈ s, b i := Finset.sum_pos hb hne
  have hs := finite_log_sum s z b hz hb hZ hB
  have hbudget' : (∑ i ∈ s, b i) ≤ V*exp (-(beta*Htop)) := by
    simpa only [b, beta, neg_mul] using hbudget
  have hl := log_sum_upper_reference hZ hB hV hbudget'
  have hid (i) (hi : i ∈ s) :
      z i*log (z i/b i) = z i*log (z i/a i^2)+beta*z i*H i := by
    rcases (hz i hi).eq_or_lt with hzero | hp
    · rw [← hzero]; ring
    · have ha2 : 0 < a i^2 := sq_pos_of_pos (ha i hi)
      rw [Real.log_div hp.ne' (hb i hi).ne',
        Real.log_div hp.ne' ha2.ne']
      dsimp [b]
      rw [Real.log_mul ha2.ne' (Real.exp_pos _).ne', Real.log_exp]
      ring
  have htilt : (∑ i ∈ s, z i*log (z i/b i)) =
      (∑ i ∈ s, z i*log (z i/a i^2))+beta*(∑ i ∈ s, z i*H i) := by
    simp_rw [Finset.sum_congr rfl hid, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [htilt] at hs
  have hlinear : (∑ i ∈ s, z i*H i) ≤ ∑ i ∈ s, a i*H i :=
    Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hza i hi) (hH i hi)
  have hm := mul_le_mul_of_nonneg_left (le_trans hl hs) (show 0 ≤ eta/2 by positivity)
  have hbeta : eta/2*beta = r := by dsimp [beta]; field_simp
  have hlin := mul_le_mul_of_nonneg_left hlinear hr
  dsimp [beta] at hl
  dsimp [beta] at hm
  have hi : eta/2*((∑ i ∈ s, z i)*log ((∑ i ∈ s, z i)/V)+
      (∑ i ∈ s, z i)*(2*r/eta*Htop)) =
      eta/2*((∑ i ∈ s, z i)*log ((∑ i ∈ s, z i)/V))+
      r*(∑ i ∈ s, z i)*Htop := by field_simp
  rw [hi] at hm
  have hj : eta/2*((∑ i ∈ s, z i*log (z i/a i^2))+
      (2*r/eta)*(∑ i ∈ s, z i*H i)) =
      eta/2*(∑ i ∈ s, z i*log (z i/a i^2))+r*(∑ i ∈ s, z i*H i) := by
    field_simp
  rw [hj] at hm
  linarith

end MostInformativeBit
