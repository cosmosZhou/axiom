import Axiom.Algebra.Pow2.gt.Zero
import Axiom.Algebra.Ne.of.Gt
open Algebra


@[main]
private lemma main
  {n : ℕ} :
-- imply
  2 ^ n ≠ 0 := by
-- proof
  have := Pow2.gt.Zero (n := n)
  exact Ne.of.Gt this


-- created on 2025-03-15
