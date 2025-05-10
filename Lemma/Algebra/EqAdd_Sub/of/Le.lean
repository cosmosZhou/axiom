import Lemma.Algebra.EqAddSub.of.Le
import Lemma.Algebra.Add.comm
open Algebra


@[main]
private lemma main
  {n m : ℕ}
-- given
  (h : m ≤ n) :
-- imply
  m + (n - m) = n := by
-- proof
  rw [Add.comm]
  apply EqAddSub.of.Le h


-- created on 2025-05-09
