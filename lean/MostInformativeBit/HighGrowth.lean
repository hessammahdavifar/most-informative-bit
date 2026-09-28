import MostInformativeBit.SpectralBaseline
import MostInformativeBit.EdgeBudget
import MostInformativeBit.RegimeAssembly

namespace MostInformativeBit
open scoped BigOperators
open ChannelProfiles

/-- The high-regime growth mechanism for actual Boolean fields. Its remaining
premises are precisely the scalar channel signs and coordinate yield comparisons. -/
theorem action_growth_of_coordinate_cost {n : ℕ} {f : Cube n → Bool}
    (hf : Monotone f) {ell D : ℝ} (hell : 31/20 ≤ ell) (hD : 2 ≤ D) :
    let r := Real.tanh ell
    let theta := Real.arcsin r
    let lam := theta/r
    let alpha := (theta+Real.sinh ell)/ell
    let gamma := lam*alpha
    let p := (lam+1/alpha)^2
    let b := lam^2*(2+1/gamma)
    let C := p*degWeight gamma D-b
    let B := 2*theta^2+C*phi r/Real.log 2
    let v := fun i => ScalarEdge.Finv (h r/(r*pivotalMean i f))
    0 ≤ C →
    0 ≤ gamma-b+C*(1/(2*Real.log 2)-1) →
    r ≤ B/ell →
    (∀ i, 0 < pivotalMean i f →
      p*deficitBound gamma D r (pivotalMean i f)+
        r*pivotalMean i f*c (v i) ≤ (B/ell)*(pivotalMean i f*v i)) →
    0 < gap f r →
    r*ell < entropyAction (noise r (signField f)) := by
  intro r theta lam alpha gamma p b C B v hC hmean hB hcost hgap
  have he : 0 < ell := by linarith
  have hr : 0 < r := CenteredSupport.tanh_pos he
  have hr1 : r < 1 := Real.tanh_lt_one ell
  have ht : 0 < theta := Real.arcsin_pos.mpr hr
  have hl : 0 < lam := div_pos ht hr
  have ha : 0 < alpha := div_pos (add_pos ht (Real.sinh_pos_iff.mpr he)) he
  have hg : 0 < gamma := mul_pos hl ha
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnc := nonconstant_of_positive_gap hgap
  have hhpos : 0 < h r := Real.binEntropy_pos (by dsimp [r]; linarith [Real.tanh_lt_one ell])
    (by dsimp [r]; linarith [Real.neg_one_lt_tanh ell])
  have hbudget : cubeExpect (fun x => h (noise r (signField f) x)) ≤ h r := by
    have hi := information_eq_phiEntropy f r
    unfold phiEntropy phi at hi
    simp only [cubeExpect_sub, cubeExpect_const, cubeExpect_noise] at hi
    have hm := phi_nonneg (cubeExpect (signField f))
    unfold phi at hm
    unfold gap at hgap
    unfold phi at hgap
    linarith
  have hv (i : Fin n) (hi : 0 < pivotalMean i f) :
      0 < v i ∧ F (v i) = h r/(r*pivotalMean i f) :=
    ScalarEdge.Finv_spec (div_pos hhpos (mul_pos hr hi))
  have hedges := EdgeBudget.edge_budget hf hnc hr hr1 hbudget v
    (fun i hi => hv i hi)
  let s := Finset.univ.filter (fun i => 0 < pivotalMean i f)
  let W := ∑ i ∈ s, pivotalMean i f*v i
  let A := entropyAction (noise r (signField f))
  let J := EdgeBudget.angleEnergy (noise r (signField f))
  have hw : W ≤ A/r := by
    apply (le_div_iff₀ hr).mpr
    have hh : r*W ≤ A := hedges.1
    nlinarith only [hh]
  have hedge : J+r*(∑ i ∈ s, pivotalMean i f*(v i-c (v i))) ≤ A :=
    hedges.2
  have hbaseline := spectral_baseline hf hell hD hC hmean
  let k := 2*gamma+C/Real.log 2
  change B-p*(∑ i, deficitBound gamma D r (pivotalMean i f))+k*gap f r ≤ J at hbaseline
  have hzero (i : Fin n) (hi : i ∉ s) : pivotalMean i f = 0 := by
    have hn : ¬0 < pivotalMean i f := by simpa [s] using hi
    exact le_antisymm (le_of_not_gt hn) (pivotalMean_nonneg hf i)
  have hsum : (∑ i, deficitBound gamma D r (pivotalMean i f)) =
      ∑ i ∈ s, deficitBound gamma D r (pivotalMean i f) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    rw [hzero i hi]
    simp [deficitBound]
  rw [hsum] at hbaseline
  have hcostsum : (∑ i ∈ s, (p*deficitBound gamma D r (pivotalMean i f)+
    r*pivotalMean i f*c (v i))) ≤ ∑ i ∈ s, B/ell*(pivotalMean i f*v i) :=
    Finset.sum_le_sum (fun i hi => hcost i (Finset.mem_filter.mp hi).2)
  have hcorr : r*(∑ i ∈ s, pivotalMean i f*(v i-c (v i))) =
      r*W-∑ i ∈ s, r*pivotalMean i f*c (v i) := by
    dsimp [W]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hcorr] at hedge
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hcostsum
  change p*(∑ i ∈ s, deficitBound gamma D r (pivotalMean i f))+
      (∑ i ∈ s, r*pivotalMean i f*c (v i)) ≤ B/ell*W at hcostsum
  have hb : B+k*gap f r+(r-B/ell)*W ≤ A := by
    nlinarith only [hbaseline, hedge, hcostsum]
  have hgrowth := growth_budget hr he hB hw hb
  have hBp : 0 < B := by
    have hh := (le_div_iff₀ he).mp hB
    exact lt_of_lt_of_le (mul_pos hr he) hh
  have hk : 0 < k := add_pos_of_pos_of_nonneg (by positivity) (div_nonneg hC hL.le)
  have hstrict : 0 < (k*ell/B)*gap f r := by positivity
  have haa : ell < A/r := by linarith
  simpa only [mul_comm] using (lt_div_iff₀ hr).mp haa

end MostInformativeBit
