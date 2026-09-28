import MostInformativeBit.ScalarEdge
import MostInformativeBit.EntropyFlow
import MostInformativeBit.MonotoneReduction

/-! Lemma `lem:edges` of mechanism.tex (the edge budget), proved by averaging the
scalar supporting-line inequalities of `ScalarEdge` over the cube edges. -/
namespace MostInformativeBit.EdgeBudget
open Set ChannelProfiles ScalarEdge
open scoped BigOperators

variable {n : ℕ}

/-- `E[Θ L Θ]` with `Θ = arcsin u`. -/
noncomputable def angleEnergy (u : Cube n → ℝ) : ℝ :=
  cubeExpect (fun x => Real.arcsin (u x) * cubeLaplacian (fun y => Real.arcsin (u y)) x)

/-- The pivotal mean `a_i = \hat f({i})` of the sign field of `f`. -/
noncomputable def pivotal (f : Cube n → Bool) (i : Fin n) : ℝ :=
  fourierCoeff (signField f) {i}

/-! ### Edge decomposition of cube averages -/

lemma cubeExpect_symm (i : Fin n) (G : Cube n → ℝ) :
    cubeExpect (fun x => (G x + G (cubeFlip i x))/2) = cubeExpect G := by
  have hf := cubeExpect_flip i G
  have he : (fun x => (G x + G (cubeFlip i x))/2) =
      fun x => (1/2:ℝ) * (G x + G (cubeFlip i x)) := by
    funext x; ring
  rw [he, cubeExpect_mul, cubeExpect_add, hf]
  ring

lemma cubeExpect_edgeAction (i : Fin n) (u : Cube n → ℝ) :
    cubeExpect (fun x => edgeAction (u x) (u (cubeFlip i x))) =
      cubeExpect (fun x => Real.artanh (u x) * cubeDerivative i u x) := by
  rw [← cubeExpect_symm i (fun x => Real.artanh (u x) * cubeDerivative i u x)]
  congr 1
  funext x
  simp only [edgeAction, cubeDerivative, cubeFlip_involutive]
  ring

lemma cubeExpect_edgeAngle (i : Fin n) (u : Cube n → ℝ) :
    cubeExpect (fun x => edgeAngle (u x) (u (cubeFlip i x))) =
      cubeExpect (fun x => Real.arcsin (u x) *
        cubeDerivative i (fun y => Real.arcsin (u y)) x) := by
  rw [← cubeExpect_symm i (fun x => Real.arcsin (u x) *
    cubeDerivative i (fun y => Real.arcsin (u y)) x)]
  congr 1
  funext x
  simp only [edgeAngle, cubeDerivative, cubeFlip_involutive]
  ring

lemma cubeExpect_edgeEntropy (i : Fin n) (u : Cube n → ℝ) :
    cubeExpect (fun x => edgeEntropy (u x) (u (cubeFlip i x))) =
      cubeExpect (fun x => h (u x)) := by
  rw [← cubeExpect_symm i (fun x => h (u x))]
  rfl

/-- `A(u) = Σ_i E a(u(x), u(x^{⊕i}))`. -/
theorem entropyAction_eq_edges (u : Cube n → ℝ) :
    entropyAction u = ∑ i, cubeExpect (fun x => edgeAction (u x) (u (cubeFlip i x))) := by
  simp only [cubeExpect_edgeAction]
  rw [← cubeExpect_sum]
  unfold entropyAction cubeLaplacian
  simp only [Finset.mul_sum]

/-- `E[Θ L Θ] = Σ_i E j(u(x), u(x^{⊕i}))`. -/
theorem angleEnergy_eq_edges (u : Cube n → ℝ) :
    angleEnergy u = ∑ i, cubeExpect (fun x => edgeAngle (u x) (u (cubeFlip i x))) := by
  simp only [cubeExpect_edgeAngle]
  rw [← cubeExpect_sum]
  unfold angleEnergy cubeLaplacian
  simp only [Finset.mul_sum]

lemma character_singleton (i : Fin n) (x : Cube n) : character {i} x = cubeSign (x i) := by
  simp [character]

/-- For a field nondecreasing in coordinate `i`, `E d_edge = \hat u({i})`. -/
theorem cubeExpect_edgeWidth (i : Fin n) {u : Cube n → ℝ}
    (hmono : ∀ y, u (Function.update y i false) ≤ u (Function.update y i true)) :
    cubeExpect (fun x => edgeWidth (u x) (u (cubeFlip i x))) = fourierCoeff u {i} := by
  unfold fourierCoeff
  simp only [character_singleton]
  rw [← cubeExpect_symm i (fun x => u x * cubeSign (x i))]
  congr 1
  funext x
  have hself : Function.update x i (x i) = x := Function.update_eq_self i x
  unfold edgeWidth
  simp only [cubeFlip_self, cubeSign_not]
  unfold cubeFlip
  cases hx : x i
  · have hm := hmono x
    rw [hx] at hself
    rw [hself] at hm
    rw [abs_of_nonpos (by simp only [Bool.not_false]; linarith)]
    simp only [cubeSign, Bool.not_false]
    norm_num
    ring
  · have hm := hmono x
    rw [hx] at hself
    rw [hself] at hm
    rw [abs_of_nonneg (by simp only [Bool.not_true]; linarith)]
    simp only [cubeSign, Bool.not_true]
    norm_num
    ring

/-- Noise preserves coordinatewise monotonicity for nonnegative correlation. -/
theorem noise_update_mono {f : Cube n → Bool} (hf : Monotone f) {r : ℝ} (hr₀ : 0 ≤ r)
    (hr₁ : r ≤ 1) (i : Fin n) (y : Cube n) :
    noise r (signField f) (Function.update y i false) ≤
      noise r (signField f) (Function.update y i true) := by
  rw [noise_section, noise_section]
  have hS := sectionNoise_mono i hr₀ hr₁ (v := signField f) (w := signField f)
    (a := false) (b := true) (fun x => by
      apply cubeSign_monotone
      apply hf
      intro j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj]) y
  simp only [Bool.not_false, Bool.not_true]
  nlinarith

/-- `E d_edge = ρ a_i` along coordinate `i` for `u = T_ρ f`, `f` monotone. -/
theorem cubeExpect_edgeWidth_noise {f : Cube n → Bool} (hf : Monotone f) {r : ℝ} (hr₀ : 0 ≤ r)
    (hr₁ : r ≤ 1) (i : Fin n) :
    cubeExpect (fun x => edgeWidth (noise r (signField f) x)
      (noise r (signField f) (cubeFlip i x))) = r * pivotal f i := by
  rw [cubeExpect_edgeWidth i (noise_update_mono hf hr₀ hr₁ i), fourierCoeff_noise]
  simp [pivotal]

/-! ### Averaging -/

/-- Averaged first supporting line along one coordinate with positive pivotal mean. -/
theorem coordinate_action_bound {f : Cube n → Bool} (hf : Monotone f) (hnc : ∃ x y, f x ≠ f y)
    {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {H : ℝ}
    (hH : cubeExpect (fun x => h (noise r (signField f) x)) ≤ H)
    (i : Fin n) (hi : 0 < pivotal f i) {v : ℝ} (hv : 0 < v) (hFv : F v = H/(r*pivotal f i)) :
    r*pivotal f i*v ≤
      cubeExpect (fun x => edgeAction (noise r (signField f) x)
        (noise r (signField f) (cubeFlip i x))) := by
  set u := noise r (signField f)
  have hu : ∀ x, u x ∈ Ioo (-1) 1 := noise_signField_mem_Ioo (by linarith) hr₁ hnc
  have hpt : ∀ x, edgeWidth (u x) (u (cubeFlip i x))*v - slopeA v*
      (edgeEntropy (u x) (u (cubeFlip i x)) - F v*edgeWidth (u x) (u (cubeFlip i x))) ≤
      edgeAction (u x) (u (cubeFlip i x)) :=
    fun x => edge_action_tangent (hu x) (hu _) hv
  have havg := cubeExpect_mono hpt
  have hlin : cubeExpect (fun x => edgeWidth (u x) (u (cubeFlip i x))*v - slopeA v*
      (edgeEntropy (u x) (u (cubeFlip i x)) - F v*edgeWidth (u x) (u (cubeFlip i x)))) =
      (cubeExpect (fun x => edgeWidth (u x) (u (cubeFlip i x))))*v - slopeA v*
      (cubeExpect (fun x => edgeEntropy (u x) (u (cubeFlip i x))) -
        F v*cubeExpect (fun x => edgeWidth (u x) (u (cubeFlip i x)))) := by
    have e1 : (fun x => edgeWidth (u x) (u (cubeFlip i x))*v - slopeA v*
        (edgeEntropy (u x) (u (cubeFlip i x)) - F v*edgeWidth (u x) (u (cubeFlip i x)))) =
        fun x => (v + slopeA v*F v)*edgeWidth (u x) (u (cubeFlip i x)) -
          slopeA v*edgeEntropy (u x) (u (cubeFlip i x)) := by
      funext x; ring
    rw [e1, cubeExpect_sub, cubeExpect_mul, cubeExpect_mul]
    ring
  rw [hlin, cubeExpect_edgeWidth_noise hf hr₀.le hr₁.le, cubeExpect_edgeEntropy, hFv,
    div_mul_cancel₀ _ (mul_pos hr₀ hi).ne'] at havg
  have hs := slopeA_pos hv
  nlinarith

/-- Averaged second supporting line along one coordinate with positive pivotal mean. -/
theorem coordinate_correction_bound {f : Cube n → Bool} (hf : Monotone f)
    (hnc : ∃ x y, f x ≠ f y) {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {H : ℝ}
    (hH : cubeExpect (fun x => h (noise r (signField f) x)) ≤ H)
    (i : Fin n) (hi : 0 < pivotal f i) {v : ℝ} (hv : 0 < v) (hFv : F v = H/(r*pivotal f i)) :
    r*pivotal f i*(v - c v) ≤
      cubeExpect (fun x => edgeAction (noise r (signField f) x)
        (noise r (signField f) (cubeFlip i x))) -
      cubeExpect (fun x => edgeAngle (noise r (signField f) x)
        (noise r (signField f) (cubeFlip i x))) := by
  set u := noise r (signField f)
  have hu : ∀ x, u x ∈ Ioo (-1) 1 := noise_signField_mem_Ioo (by linarith) hr₁ hnc
  have hpt : ∀ x, edgeWidth (u x) (u (cubeFlip i x))*(v - c v) - slopeC v*
      (edgeEntropy (u x) (u (cubeFlip i x)) - F v*edgeWidth (u x) (u (cubeFlip i x))) ≤
      edgeAction (u x) (u (cubeFlip i x)) - edgeAngle (u x) (u (cubeFlip i x)) :=
    fun x => edge_correction_tangent (hu x) (hu _) hv
  have havg := cubeExpect_mono hpt
  have hlin : cubeExpect (fun x => edgeWidth (u x) (u (cubeFlip i x))*(v - c v) - slopeC v*
      (edgeEntropy (u x) (u (cubeFlip i x)) - F v*edgeWidth (u x) (u (cubeFlip i x)))) =
      (cubeExpect (fun x => edgeWidth (u x) (u (cubeFlip i x))))*(v - c v) - slopeC v*
      (cubeExpect (fun x => edgeEntropy (u x) (u (cubeFlip i x))) -
        F v*cubeExpect (fun x => edgeWidth (u x) (u (cubeFlip i x)))) := by
    have e1 : (fun x => edgeWidth (u x) (u (cubeFlip i x))*(v - c v) - slopeC v*
        (edgeEntropy (u x) (u (cubeFlip i x)) - F v*edgeWidth (u x) (u (cubeFlip i x)))) =
        fun x => (v - c v + slopeC v*F v)*edgeWidth (u x) (u (cubeFlip i x)) -
          slopeC v*edgeEntropy (u x) (u (cubeFlip i x)) := by
      funext x; ring
    rw [e1, cubeExpect_sub, cubeExpect_mul, cubeExpect_mul]
    ring
  have hsub : cubeExpect (fun x => edgeAction (u x) (u (cubeFlip i x)) -
      edgeAngle (u x) (u (cubeFlip i x))) =
      cubeExpect (fun x => edgeAction (u x) (u (cubeFlip i x))) -
      cubeExpect (fun x => edgeAngle (u x) (u (cubeFlip i x))) := cubeExpect_sub _ _
  rw [hlin, hsub, cubeExpect_edgeWidth_noise hf hr₀.le hr₁.le, cubeExpect_edgeEntropy, hFv,
    div_mul_cancel₀ _ (mul_pos hr₀ hi).ne'] at havg
  have hs := slopeC_nonneg v
  nlinarith

/-- **Lemma `lem:edges` (the edge budget).** For a nonconstant monotone Boolean `f`,
`0 < ρ < 1`, `u = T_ρ f`, any budget `H ≥ E h(u)`, and heights `v_i > 0` with
`F(v_i) = H/(ρ a_i)` for every `i` with `a_i > 0`:
`A(u) ≥ ρ Σ a_i v_i` and `A(u) ≥ E[Θ L Θ] + ρ Σ a_i (v_i - c(v_i))`,
the sums ranging over `a_i > 0`. -/
theorem edge_budget {f : Cube n → Bool} (hf : Monotone f) (hnc : ∃ x y, f x ≠ f y)
    {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {H : ℝ}
    (hH : cubeExpect (fun x => h (noise r (signField f) x)) ≤ H)
    (v : Fin n → ℝ)
    (hv : ∀ i, 0 < pivotal f i → 0 < v i ∧ F (v i) = H/(r*pivotal f i)) :
    r*∑ i ∈ Finset.univ.filter (fun i => 0 < pivotal f i), pivotal f i*v i ≤
        entropyAction (noise r (signField f)) ∧
    angleEnergy (noise r (signField f)) +
        r*∑ i ∈ Finset.univ.filter (fun i => 0 < pivotal f i), pivotal f i*(v i - c (v i)) ≤
        entropyAction (noise r (signField f)) := by
  set u := noise r (signField f)
  have hu : ∀ x, u x ∈ Ioo (-1) 1 := noise_signField_mem_Ioo (by linarith) hr₁ hnc
  constructor
  · rw [entropyAction_eq_edges, Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro i _
    split_ifs with hi
    · have hb := coordinate_action_bound hf hnc hr₀ hr₁ hH i hi (hv i hi).1 (hv i hi).2
      calc r*(pivotal f i*v i) = r*pivotal f i*v i := by ring
        _ ≤ _ := hb
    · exact cubeExpect_nonneg (fun x => edgeAction_nonneg (hu x) (hu _))
  · rw [entropyAction_eq_edges, angleEnergy_eq_edges, Finset.mul_sum, Finset.sum_filter]
    have key : (∑ i, if 0 < pivotal f i then r*(pivotal f i*(v i - c (v i))) else 0) ≤
        ∑ i, (cubeExpect (fun x => edgeAction (u x) (u (cubeFlip i x))) -
          cubeExpect (fun x => edgeAngle (u x) (u (cubeFlip i x)))) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hi
      · have hb := coordinate_correction_bound hf hnc hr₀ hr₁ hH i hi (hv i hi).1 (hv i hi).2
        nlinarith
      · have := cubeExpect_mono (fun x => edgeAngle_le_edgeAction (hu x) (hu (cubeFlip i x)))
        linarith
    rw [Finset.sum_sub_distrib] at key
    linarith

/-- Existence and uniqueness of the heights of Lemma `lem:edges` when `H > 0`
(in particular when `H ≥ E h(u) > 0`), via `ChannelBounds.existsUnique_height`. -/
theorem existsUnique_heights {f : Cube n → Bool} {r H : ℝ} (hr₀ : 0 < r) (hH : 0 < H)
    (i : Fin n) (hi : 0 < pivotal f i) :
    ∃! v : ℝ, 0 < v ∧ F v = H/(r*pivotal f i) :=
  ChannelBounds.existsUnique_height (div_pos hH (mul_pos hr₀ hi))

/-- Lemma `lem:edges` as stated in the source, with the unique heights `v_i = F⁻¹(H/(ρ a_i))`
and hypothesis `H ≥ E h(u) > 0`. -/
theorem edge_budget_source {f : Cube n → Bool} (hf : Monotone f) (hnc : ∃ x y, f x ≠ f y)
    {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {H : ℝ}
    (hH : cubeExpect (fun x => h (noise r (signField f) x)) ≤ H)
    (hpos : 0 < cubeExpect (fun x => h (noise r (signField f) x))) :
    r*∑ i ∈ Finset.univ.filter (fun i => 0 < pivotal f i),
        pivotal f i*Finv (H/(r*pivotal f i)) ≤ entropyAction (noise r (signField f)) ∧
    angleEnergy (noise r (signField f)) +
        r*∑ i ∈ Finset.univ.filter (fun i => 0 < pivotal f i),
          pivotal f i*(Finv (H/(r*pivotal f i)) - c (Finv (H/(r*pivotal f i)))) ≤
        entropyAction (noise r (signField f)) :=
  edge_budget hf hnc hr₀ hr₁ hH (fun i => Finv (H/(r*pivotal f i)))
    (fun _ hi => Finv_spec (div_pos (lt_of_lt_of_le hpos hH) (mul_pos hr₀ hi)))

end MostInformativeBit.EdgeBudget
