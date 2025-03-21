import Axiom.Algebra.Pow2.gt.Zero
import Axiom.Algebra.Ge_Add_1.of.Gt
import Axiom.Algebra.EqAdd0
open Algebra


@[main]
private lemma main
  {n : ℕ} :
-- imply
  2 ^ n ≥ 1 := by
-- proof
  have := Pow2.gt.Zero (n := n)
  have := Ge_Add_1.of.Gt this
  rw [EqAdd0] at this
  assumption


-- created on 2025-03-15
