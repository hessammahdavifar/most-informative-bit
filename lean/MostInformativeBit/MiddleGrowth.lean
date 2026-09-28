import MostInformativeBit.AngularPivotal
import MostInformativeBit.MiddleBudget
import MostInformativeBit.EdgeBudget
import MostInformativeBit.MiddleChannel
import MostInformativeBit.RegimeAssembly
import MostInformativeBit.LowRegime

/-! Proposition `prop:middle-growth` of mechanism.tex (intermediate-correlation
growth), assembled from the actual cube components: the pivotal angular baseline
(`angular_pivotal_baseline`), the edge budget (`EdgeBudget.edge_budget`), the
channel checks (`MiddleChannel.middle_channel_checks`) and the finite log-sum
closure (`middle_pivotal_closure`). No analytic hypothesis remains. -/
namespace MostInformativeBit
open scoped BigOperators
open Real

/-! ### Scalar facts for the middle range -/

/-- `h(tanh v) < 1/2` for `v ≥ 31/20` (the source's `h(r) < 1/2`). -/
theorem h_tanh_lt_half {v : ℝ} (hv : 31/20 ≤ v) : h (Real.tanh v) < 1/2 := by
  rw [ChannelBounds.h_tanh_eq_q]
  set q := ChannelBounds.q v with hq
  have hq0 : 0 < q := ChannelBounds.q_pos v
  have hlog : Real.log (1+q) ≤ q := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1+q); linarith
  have hfrac : 2*v*q/(1+q) ≤ 2*v*q := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_pos (mul_pos (by linarith : (0:ℝ) < v) hq0) hq0]
  have hexp : 2*(1+2*v) < Real.exp (2*v) := by
    have h1 := CenteredSupport.exp_threshold
    have h2 := Real.add_one_le_exp (2*v - 31/10)
    have h3 : Real.exp (2*v) = Real.exp (31/10) * Real.exp (2*v - 31/10) := by
      rw [← Real.exp_add]; ring_nf
    rw [h3]
    have h4 : 0 < 2*v - 31/10 + 1 := by linarith
    nlinarith
  have hqe : q * Real.exp (2*v) = 1 := by
    rw [hq, ChannelBounds.q, ← Real.exp_add]; simp
  have : q*(1+2*v) < 1/2 := by nlinarith
  nlinarith

/-- `E h(u) = h(r) - φ(m) - Δ`, from the posterior identity. -/
theorem cubeExpect_h_noise {n : ℕ} (f : Cube n → Bool) (r : ℝ) :
    cubeExpect (fun x => h (noise r (signField f) x)) =
      h r - phi (cubeExpect (signField f)) - gap f r := by
  have hi := information_eq_phiEntropy f r
  have hh : (fun x => h (noise r (signField f) x)) =
      fun x => Real.log 2 - phi (noise r (signField f) x) := by
    funext x; unfold phi; ring
  rw [hh, cubeExpect_sub, cubeExpect_const]
  unfold gap phi at *
  unfold phiEntropy at hi
  rw [cubeExpect_noise] at hi
  unfold phi at hi
  linarith

theorem lam_sq_identity (θ : ℝ) {s c : ℝ} (hs : s ≠ 0) (hc : c ≠ 0) (hcs : c^2 = 1 + s^2) :
    (θ/(s/c))^2*(2-(s/c)^2) = θ^2 + 2*θ^2/s^2 := by
  field_simp
  rw [hcs]; ring

/-! ### The middle proposition -/

/-- **Proposition `prop:middle-growth`, action form.** For every monotone Boolean
`f` and `31/20 ≤ ℓ ≤ 7/2`, with `r = tanh ℓ`, a positive information gap forces
`A(u) > r ℓ` for `u = T_r f`. -/
theorem middle_action_growth {n : ℕ} {f : Cube n → Bool} (hf : Monotone f)
    {ell : ℝ} (hl : 31/20 ≤ ell) (hu : ell ≤ 7/2)
    (hgap : 0 < gap f (Real.tanh ell)) :
    Real.tanh ell * ell < entropyAction (noise (Real.tanh ell) (signField f)) := by
  set r := Real.tanh ell with hrdef
  set u := noise r (signField f) with hudef
  set m := cubeExpect (signField f) with hmdef
  set V := meanDefect f with hVdef
  set theta := Real.arcsin r with hθ
  set lam := theta/r with hlam
  set alpha := (theta+Real.sinh ell)/ell with halpha
  set gamma := lam*alpha with hgamma
  set eta := theta^2*gamma/(gamma+1) with heta
  set M := 2*gamma*phi m-(lam^2*(2-r^2)+lam/alpha)*m^2 with hM
  have hell : 0 < ell := by linarith
  have hellI : ell ∈ Set.Icc ((31:ℝ)/20) ((7:ℝ)/2) := ⟨hl, hu⟩
  have hr0 : 0 < r := CenteredSupport.tanh_pos hell
  have hr1 : r < 1 := Real.tanh_lt_one ell
  have hnc := nonconstant_of_positive_gap hgap
  -- parameters agree with MiddleChannel's
  have hθc : ChannelProfiles.theta ell = theta := rfl
  have hrc : MiddleChannel.r ell = r := rfl
  have hgc : MiddleChannel.gamma ell = gamma := rfl
  have hec : MiddleChannel.eta ell = eta := by
    show ChannelProfiles.theta ell ^ 2 * (MiddleChannel.gamma ell / (MiddleChannel.gamma ell + 1)) = eta
    rw [hgc, hθc, heta]; ring
  have hg0 : 0 < gamma := MiddleChannel.gamma_pos hell
  have he0 : 0 < eta := by rw [← hec]; exact MiddleChannel.eta_pos hell
  have hθ0 : 0 < theta := ChannelProfiles.theta_pos hell
  -- mean and pivotal bounds
  have hmI : |m| ≤ 1 := by
    have := cubeExpect_mem_Icc (fun x => signField_mem_Icc f x)
    exact abs_le.mpr ⟨this.1, this.2⟩
  have hV0 : 0 < V := by
    have hZ := pivotalTotal_pos hg0 hr0 hnc
    exact lt_of_lt_of_le hZ ((pivotalTotal_le_noisyVarRatio hg0 hr0 f).trans
      (noisyVarRatio_le_meanDefect hr0 hr1.le f))
  have hVm : V = 1 - m^2 := rfl
  have haV : ∀ i, pivotalMean i f ≤ V := by
    intro i
    have h1 := mean_abs_add_singleton_abs_le_one i (signField_mem_Icc f)
    rw [← hmdef] at h1
    have h2 : fourierCoeff (signField f) {i} ≤ |fourierCoeff (signField f) {i}| := le_abs_self _
    have h3 : 1 - |m| ≤ 1 - m^2 := by
      have : m^2 = |m|^2 := (sq_abs m).symm
      nlinarith [abs_nonneg m]
    rw [hVm]; show fourierCoeff (signField f) {i} ≤ 1 - m^2; linarith
  -- the entropy budget H = V h(r)
  have hhr : h r < 1/2 := h_tanh_lt_half hl
  have hhr0 : 0 < h r := ChannelProfiles.h_tanh_pos ell
  have hbudget : cubeExpect (fun x => h (u x)) ≤ V * h r := by
    rw [hudef, cubeExpect_h_noise]
    have hq := phi_quadratic_lower hmI
    rw [hVm]
    nlinarith [sq_nonneg m]
  have hB0 : 0 < V * h r := mul_pos hV0 hhr0
  have hFell : ChannelProfiles.F ell = h r / r := rfl
  have hF0 : 0 < ChannelProfiles.F ell := ChannelProfiles.F_pos hell
  -- heights
  set v : Fin n → ℝ := fun i => ScalarEdge.Finv (V * h r / (r * pivotalMean i f)) with hvdef
  have hvspec : ∀ i, 0 < pivotalMean i f →
      0 < v i ∧ ChannelProfiles.F (v i) = V * h r / (r * pivotalMean i f) :=
    fun i hi => ScalarEdge.Finv_spec (div_pos hB0 (mul_pos hr0 hi))
  have hheight : ∀ i, 0 < pivotalMean i f →
      ChannelProfiles.F (v i) = V * ChannelProfiles.F ell / pivotalMean i f := by
    intro i hi
    rw [(hvspec i hi).2, hFell]
    field_simp
  have hvle : ∀ i, 0 < pivotalMean i f → v i ≤ ell := by
    intro i hi
    by_contra hlt
    push Not at hlt
    have hanti := ChannelProfiles.F_strictAnti (Set.mem_Ioi.mpr hell)
      (Set.mem_Ioi.mpr (hvspec i hi).1) hlt
    rw [hheight i hi] at hanti
    have : ChannelProfiles.F ell ≤ V * ChannelProfiles.F ell / pivotalMean i f := by
      rw [le_div_iff₀ hi, mul_comm V]; exact mul_le_mul_of_nonneg_left (haV i) hF0.le
    linarith
  -- contradiction hypothesis
  by_contra hA
  push Not at hA
  have hedge := EdgeBudget.edge_budget hf hnc hr0 hr1 hbudget v (fun i hi => hvspec i hi)
  set s := Finset.univ.filter (fun i : Fin n => 0 < pivotalMean i f) with hs
  have hsEB : Finset.univ.filter (fun i : Fin n => 0 < EdgeBudget.pivotal f i) = s := rfl
  rw [hsEB] at hedge
  have hweight : (∑ i ∈ s, pivotalMean i f * v i) ≤ ell := by
    have := hedge.1.trans hA
    change r * ∑ i ∈ s, pivotalMean i f * v i ≤ r * ell at this
    exact le_of_mul_le_mul_left this hr0
  -- inactive coordinates contribute zero
  have hzero : ∀ i, ¬ 0 < pivotalMean i f → pivotalAverage gamma r i f = 0 := by
    intro i hi
    have ha0 : pivotalMean i f = 0 := le_antisymm (not_lt.mp hi) (pivotalMean_nonneg hf i)
    exact pivotalAverage_eq_zero_of_mean hg0 hr0 hr1.le hf i ha0
  have hZs : (∑ i ∈ s, pivotalAverage gamma r i f) = pivotalTotal gamma r f := by
    unfold pivotalTotal
    rw [hs, Finset.sum_filter_of_ne]
    intro i _ hne
    by_contra hi; exact hne (hzero i hi)
  have hEs : (∑ i ∈ s, pivotalAverage gamma r i f *
        Real.log (pivotalAverage gamma r i f / pivotalMean i f ^ 2)) =
      ∑ i, pivotalAverage gamma r i f *
        Real.log (pivotalAverage gamma r i f / pivotalMean i f ^ 2) := by
    rw [hs, Finset.sum_filter_of_ne]
    intro i _ hne
    by_contra hi; exact hne (by rw [hzero i hi]; simp)
  -- baseline
  have hbase := angular_pivotal_baseline hf hl
  dsimp only at hbase
  rw [← hZs, ← hEs] at hbase
  -- channel checks
  have hprof : ∀ i ∈ s, (2*r/eta) * (MiddleChannel.H ell - MiddleChannel.H (v i)) ≤
      Real.log (v i * ChannelProfiles.F (v i) / (ell * ChannelProfiles.F ell)) := by
    intro i hi
    have hi' : 0 < pivotalMean i f := (Finset.mem_filter.mp hi).2
    have hp := MiddleChannel.middle_profile hellI ⟨(hvspec i hi').1, hvle i hi'⟩
    rwa [MiddleChannel.beta, hrc, hec] at hp
  have hcr : r * ChannelProfiles.c ell = theta^2 := by
    unfold ChannelProfiles.c; rw [hθc, ← hrdef]; field_simp
  have hidentity : r * ell = theta^2 + r * MiddleChannel.H ell := by
    unfold MiddleChannel.H; rw [mul_sub, hcr]; ring
  have henergy : 0 ≤ theta^2 - r * MiddleChannel.H ell - eta/2 := by
    have := MiddleChannel.middle_energy hellI
    rwa [hθc, hrc, hec] at this
  have hmean : 0 ≤ M - r * MiddleChannel.H ell * m^2 := by
    have hmm := MiddleChannel.middle_mean hellI
    rw [hrc, hθc, hgc] at hmm
    change r * ell ≤ gamma - 2*theta^2/(Real.sinh ell)^2 - lam/alpha at hmm
    have hq := phi_quadratic_lower hmI
    have hsh : 0 < Real.sinh ell := Real.sinh_pos_iff.mpr hell
    have hch : 0 < Real.cosh ell := Real.cosh_pos ell
    have hlam2 : lam^2*(2-r^2) = theta^2 + 2*theta^2/(Real.sinh ell)^2 := by
      have h := lam_sq_identity theta hsh.ne' hch.ne' (by rw [Real.cosh_sq]; ring)
      rw [← Real.tanh_eq_sinh_div_cosh] at h
      exact h
    have hkey : 0 ≤ gamma - lam^2*(2-r^2) - lam/alpha - (r*ell - theta^2) := by
      linarith [hlam2, hmm]
    have hrH : r * MiddleChannel.H ell = r*ell - theta^2 := by linarith [hidentity]
    have hrH2 : r * MiddleChannel.H ell * m^2 = (r*ell - theta^2)*m^2 := by rw [hrH]
    have hg2 : gamma*m^2 ≤ gamma*(2*phi m) :=
      mul_le_mul_of_nonneg_left (by linarith [hq]) hg0.le
    have hkm := mul_nonneg hkey (sq_nonneg m)
    have hMe : M = 2*gamma*phi m-(lam^2*(2-r^2)+lam/alpha)*m^2 := rfl
    linarith only [hkm, hg2, hMe, hrH2]
  have hHnn : ∀ i ∈ s, 0 ≤ MiddleChannel.H (v i) := by
    intro i hi
    have hi' : 0 < pivotalMean i f := (Finset.mem_filter.mp hi).2
    unfold MiddleChannel.H
    linarith [ChannelProfiles.c_le_self (hvspec i hi').1.le]
  have hedge2 : EdgeBudget.angleEnergy u + r * ∑ i ∈ s, pivotalMean i f * MiddleChannel.H (v i)
      ≤ entropyAction u := hedge.2
  have hZV : (∑ i ∈ s, pivotalAverage gamma r i f) ≤ V := by
    rw [hZs]
    exact (pivotalTotal_le_noisyVarRatio hg0 hr0 f).trans
      (noisyVarRatio_le_meanDefect hr0 hr1.le f)
  have hZpos : 0 < ∑ i ∈ s, pivotalAverage gamma r i f := by
    rw [hZs]; exact pivotalTotal_pos hg0 hr0 hnc
  have hgrowth := middle_pivotal_closure s
    (fun i => pivotalAverage gamma r i f) (fun i => pivotalMean i f) v
    (fun i => ChannelProfiles.F (v i)) (fun i => MiddleChannel.H (v i))
    (action := entropyAction u) (angular := EdgeBudget.angleEnergy u)
    (theta := theta) (meanCorrection := M)
    hr0 he0 hg0 hgap hV0 hell hF0
    (fun i hi => (Finset.mem_filter.mp hi).2)
    (fun i hi => (hvspec i (Finset.mem_filter.mp hi).2).1)
    (fun i _ => le_trans (sq_nonneg _) (pivotalAverage_bounds hg0 hr0 hr1.le hf i).1)
    (fun i _ => (pivotalAverage_bounds hg0 hr0 hr1.le hf i).2)
    hHnn hZpos hZV hVm
    (fun i hi => hheight i (Finset.mem_filter.mp hi).2)
    hprof hweight hidentity henergy hmean hbase hedge2
  linarith

/-- **Proposition `prop:middle-growth`.** For every monotone Boolean `f` and
`31/20 ≤ ℓ ≤ 7/2`, `Δ_f(r) > 0` at `r = tanh ℓ` implies `I_f'(r) > φ'(r)`,
stated as positivity of the derivative of the gap `Δ_f = I_f - φ`. -/
theorem middle_growth {n : ℕ} {f : Cube n → Bool} (hf : Monotone f)
    {ell : ℝ} (hl : 31/20 ≤ ell) (hu : ell ≤ 7/2)
    (hgap : 0 < gap f (Real.tanh ell)) :
    0 < deriv (gap f) (Real.tanh ell) := by
  have hell : 0 < ell := by linarith
  apply positive_gap_derivative_of_action (CenteredSupport.tanh_pos hell)
    (Real.tanh_lt_one ell) hgap
  rw [Real.artanh_tanh]
  exact middle_action_growth hf hl hu hgap

/-- **Proposition `prop:middle-growth`, literal form** `I_f'(r) > φ'(r)`. -/
theorem middle_growth_deriv {n : ℕ} {f : Cube n → Bool} (hf : Monotone f)
    {ell : ℝ} (hl : 31/20 ≤ ell) (hu : ell ≤ 7/2)
    (hgap : 0 < gap f (Real.tanh ell)) :
    deriv phi (Real.tanh ell) < deriv (information f) (Real.tanh ell) := by
  have hell : 0 < ell := by linarith
  have hr0 : 0 < Real.tanh ell := CenteredSupport.tanh_pos hell
  have hr1 : Real.tanh ell < 1 := Real.tanh_lt_one ell
  have hnc := nonconstant_of_positive_gap hgap
  have hI := phiEntropy_noise_hasDerivAt (signField f) hr0.ne'
    (noise_signField_mem_Ioo (by linarith) hr1 hnc)
  have he : information f = fun t => phiEntropy (noise t (signField f)) :=
    funext (information_eq_phiEntropy f)
  rw [← he] at hI
  have hφ := phi_hasDerivAt (by linarith : -1 < Real.tanh ell) hr1
  rw [hI.deriv, hφ.deriv, Real.artanh_tanh, lt_div_iff₀ hr0, mul_comm]
  exact middle_action_growth hf hl hu hgap

end MostInformativeBit
