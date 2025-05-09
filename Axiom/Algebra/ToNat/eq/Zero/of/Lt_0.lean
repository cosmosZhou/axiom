import Axiom.Algebra.Le.of.Lt
import Axiom.Algebra.ToNat.eq.Zero.of.Le_0
open Algebra


@[main]
private lemma main
  {n : ℤ}
-- given
  (h : n < 0) :
-- imply
  n.toNat = 0 := by
-- proof
  have h := Le.of.Lt h
  apply ToNat.eq.Zero.of.Le_0 h


-- created on 2025-05-05
