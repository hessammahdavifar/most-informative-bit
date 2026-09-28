import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! The last argument in mechanism.tex, fully quantified over real functions.
The positive-derivative hypothesis is explicit; this module does not prove
the paper's essential growth lemma for Boolean mutual information.
-/
namespace MostInformativeBit

theorem nonpositive_of_positive_derivative_on_positive_set
    {f : ℝ → ℝ}
    (hc : ContinuousOn f (Set.Icc 0 1))
    (h0 : f 0 ≤ 0) (h1 : f 1 ≤ 0)
    (hg : ∀ x ∈ Set.Ioo 0 1, 0 < f x → 0 < deriv f x) :
    ∀ x ∈ Set.Icc 0 1, f x ≤ 0 := by
  intro x hx
  by_contra h
  have hpos : 0 < f x := lt_of_not_ge h
  obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Set.Icc (0:ℝ) 1).Nonempty from ⟨0, by norm_num⟩) hc
  have hyp : 0 < f y := lt_of_lt_of_le hpos (hmax hx)
  have hy0 : 0 < y := by
    have hne : y ≠ 0 := by intro he; subst y; linarith
    exact lt_of_le_of_ne hy.1 (Ne.symm hne)
  have hy1 : y < 1 := by
    have hne : y ≠ 1 := by intro he; subst y; linarith
    exact lt_of_le_of_ne hy.2 hne
  have he : deriv f y = 0 :=
    (hmax.isLocalMax (Icc_mem_nhds hy0 hy1)).deriv_eq_zero
  have hp := hg y ⟨hy0, hy1⟩ hyp
  linarith

end MostInformativeBit
