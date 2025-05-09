import Axiom.Algebra.Eq_ToNat.of.Ge_0
import Axiom.Algebra.Ge.of.Gt
open Algebra


@[main]
private lemma main
  {n : ℤ}
-- given
  (h : n > 0) :
-- imply
  n = n.toNat := by
-- proof
  have h := Ge.of.Gt h
  apply Eq_ToNat.of.Ge_0 h


-- created on 2025-05-04
