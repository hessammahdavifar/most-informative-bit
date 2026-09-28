import MostInformativeBit.Vendor.GeneralCK.Statement

/-! Complementing every channel output exchanges crossover probabilities `p`
and `1-p`, without changing the information carried by the output. -/

namespace GeneralCK
open scoped BigOperators

/-- The bijection that complements every output bit, including the empty cube. -/
def cubeComplementEquiv (n : ℕ) : Cube n ≃ Cube n where
  toFun x i := !(x i)
  invFun x i := !(x i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

theorem noiseKernel_complement {n : ℕ} (p : ℝ) (x y : Cube n) :
    noiseKernel (1-p) x y = noiseKernel p x (cubeComplementEquiv n y) := by
  classical
  unfold noiseKernel
  apply Finset.prod_congr rfl
  intro i _
  cases x i <;> cases hy : y i <;> simp [cubeComplementEquiv, hy]

theorem jointMass_complement {n : ℕ} (f : Cube n → Bool) (p : ℝ)
    (b : Bool) (y : Cube n) :
    jointMass f (1-p) b y = jointMass f p b (cubeComplementEquiv n y) := by
  simp only [jointMass, noiseKernel_complement]

/-- Finite entropy is invariant under a bijective relabeling. -/
theorem entropy_comp_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (q : β → ℝ) : entropy (fun a => q (e a)) = entropy q := by
  exact congrArg (fun s : ℝ => s / Real.log 2)
    (e.sum_comp (fun b => Real.negMulLog (q b)))

/-- Output complementation preserves the actual finite-distribution information. -/
theorem mutualInformation_complement {n : ℕ} (f : Cube n → Bool) (p : ℝ) :
    mutualInformation f (1-p) = mutualInformation f p := by
  classical
  unfold mutualInformation
  simp_rw [jointMass_complement]
  have hm (b : Bool) :
      (∑ y, jointMass f p b (cubeComplementEquiv n y)) = ∑ y, jointMass f p b y :=
    (cubeComplementEquiv n).sum_comp _
  simp_rw [hm]
  rw [entropy_comp_equiv (cubeComplementEquiv n)
    (fun y => ∑ b, jointMass f p b y)]
  congr 1
  exact entropy_comp_equiv ((Equiv.refl Bool).prodCongr (cubeComplementEquiv n))
    (fun byPair => jointMass f p byPair.1 byPair.2)

end GeneralCK
