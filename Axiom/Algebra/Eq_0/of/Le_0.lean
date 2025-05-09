import Axiom.Algebra.Ge_0
import Axiom.Algebra.Eq.of.Ge.Le
open Algebra


@[main]
private lemma main
  {n : ℕ}
-- given
  (h : n ≤ 0) :
-- imply
  n = 0 := by
-- proof
  have := Ge_0 (n := n)
  apply Eq.of.Ge.Le this h


-- created on 2025-04-12
