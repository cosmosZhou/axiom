import Axiom.Algebra.Eq_Neg.of.Add.eq.Zero
import Axiom.Algebra.Eq.of.Ne_0.EqMulS
import Axiom.Algebra.EqMul_Div.of.Ne_0
import Axiom.Algebra.Eq_Add.of.EqSub
import Axiom.Algebra.Mul.comm
open Algebra


/--
In a field `α`, the equation `0 = a * x + b` with `a ≠ 0` has exactly one solution, `x = -b / a`,
hence the solution set `{x | 0 = a * x + b}` equals `{-b / a}`.
- given
  - h : a ≠ 0
- imply
  - {x | 0 = a * x + b} = {-b / a}
-/
@[main]
private lemma main
  [Field α]
  {a b : α}
-- given
  (h : a ≠ 0) :
-- imply
  {x | 0 = a * x + b} = {-b / a} := by
-- proof
  ext x
  constructor <;>
    intro h_In
  ·
    -- Given 0 = a * x + b, solve for x and show x ∈ {-b / a}
    field_simp [h] at h_In
    simp
    apply Eq.of.Ne_0.EqMulS (h₀ := h)
    simp [EqMul_Div.of.Ne_0 h]
    apply Eq_Neg.of.Add.eq.Zero
    exact h_In.symm
  ·
    -- Given x = -b / a, substitute and verify 0 = a * x + b
    field_simp [h] at h_In
    simp
    apply Eq_Add.of.EqSub
    simp
    rw [Mul.comm]
    exact h_In.symm


-- created on 2025-04-02
-- updated on 2025-04-03
