import sympy.core.relational
import sympy.sets.sets
import Axiom.Algebra.EqAddSub.of.Le
import Axiom.Algebra.Add.comm
import Axiom.Algebra.EqAddS.of.Eq
import Axiom.Algebra.EqSubAdd
open Algebra


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h : n > 0) :
-- imply
  ∑ i ∈ range n, x i = x 0 + ∑ i ∈ Finset.Ico 1 n, x i := by
-- proof
  -- Split the sum into the first term and the rest
  denote h_n' : n' = n - 1
  have h_n : n = n' + 1 := by 
    simp [h_n']
    simp [EqAddSub.of.Le (by linarith [h] : 1 ≤ n)]
  rw [h_n]
  rw [Finset.sum_range_succ']
  rw [Add.comm]
  apply EqAddS.of.Eq.left
  rw [Finset.sum_Ico_eq_sum_range]
  simp [EqSubAdd.int]
  simp [Add.comm]


-- created on 2025-04-06
-- updated on 2025-04-26
