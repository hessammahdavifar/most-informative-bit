import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-! Elementary interval arithmetic, used to emit proof certificates rather than
trust numerical computations. All bounds are ordinary real inequalities.
-/
namespace MostInformativeBit.IntervalBounds

def Encloses (x lo hi : ℝ) : Prop := lo ≤ x ∧ x ≤ hi

theorem exact_value (x : ℝ) : Encloses x x x := ⟨le_rfl, le_rfl⟩

theorem weaken {x lo hi lo' hi' : ℝ} (hx : Encloses x lo hi)
    (hl : lo' ≤ lo) (hu : hi ≤ hi') : Encloses x lo' hi' :=
  ⟨le_trans hl hx.1, le_trans hx.2 hu⟩

theorem add {x y lo hi lo' hi' : ℝ}
    (hx : Encloses x lo hi) (hy : Encloses y lo' hi') :
    Encloses (x+y) (lo+lo') (hi+hi') := by
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem neg {x lo hi : ℝ} (hx : Encloses x lo hi) : Encloses (-x) (-hi) (-lo) :=
  ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩

theorem sub {x y lo hi lo' hi' : ℝ}
    (hx : Encloses x lo hi) (hy : Encloses y lo' hi') :
    Encloses (x-y) (lo-hi') (hi-lo') := by
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem mul_nonneg {x y lo hi lo' hi' : ℝ}
    (hx : Encloses x lo hi) (hy : Encloses y lo' hi')
    (hl : 0 ≤ lo) (hl' : 0 ≤ lo') :
    Encloses (x*y) (lo*lo') (hi*hi') := by
  constructor
  · exact mul_le_mul hx.1 hy.1 hl' (le_trans hl hx.1)
  · exact mul_le_mul hx.2 hy.2 (le_trans hl' hy.1) (le_trans hl (le_trans hx.1 hx.2))

theorem inv_pos {x lo hi : ℝ} (hx : Encloses x lo hi) (hl : 0 < lo) :
    Encloses (1/x) (1/hi) (1/lo) := by
  constructor
  · exact one_div_le_one_div_of_le (lt_of_lt_of_le hl hx.1) hx.2
  · exact one_div_le_one_div_of_le hl hx.1

theorem div_nonneg {x y lo hi lo' hi' : ℝ}
    (hx : Encloses x lo hi) (hy : Encloses y lo' hi')
    (hl : 0 ≤ lo) (hl' : 0 < lo') :
    Encloses (x/y) (lo/hi') (hi/lo') := by
  have hhi : 0 < hi' := lt_of_lt_of_le hl' (le_trans hy.1 hy.2)
  have hh := mul_nonneg hx (inv_pos hy hl') hl
    (show 0 ≤ 1/hi' by positivity)
  simpa only [div_eq_mul_inv, one_mul] using hh

theorem pow_nonneg {x lo hi : ℝ} (hx : Encloses x lo hi) (hl : 0 ≤ lo) (n : ℕ) :
    Encloses (x^n) (lo^n) (hi^n) := by
  exact ⟨pow_le_pow_left₀ hl hx.1 n,
    pow_le_pow_left₀ (le_trans hl hx.1) hx.2 n⟩

theorem log {x lo hi llog ulog : ℝ} (hx : Encloses x lo hi) (hl : 0 < lo)
    (hll : llog ≤ Real.log lo) (hul : Real.log hi ≤ ulog) :
    Encloses (Real.log x) llog ulog :=
  ⟨le_trans hll (Real.log_le_log hl hx.1),
    le_trans (Real.log_le_log (lt_of_lt_of_le hl hx.1) hx.2) hul⟩

end MostInformativeBit.IntervalBounds
