import Axiom.Algebra.OrAndS.of.And_Or
import Axiom.Algebra.AndAndNot.equ.False
import Axiom.Algebra.AndAnd_Not.equ.False
open Algebra


@[main]
private lemma main
-- given
  (h : ¬p ∧ ¬q) :
-- imply
  ¬(p ∨ q) := by
-- proof
  by_contra h_Or
  have h := And.intro h h_Or
  have h := OrAndS.of.And_Or h
  simp at h


-- created on 2024-07-01
