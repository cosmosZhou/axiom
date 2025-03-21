import Axiom.Algebra.And_Or.equ.OrAndS
import Axiom.Algebra.AndAnd__Not.equ.False
open Algebra


@[main]
private lemma main
-- given
  (h : ¬p ∨ ¬q) :
-- imply
  ¬(p ∧ q) := by
-- proof
  intro hpq
  have h := And.intro hpq h
  rw [And_Or.equ.OrAndS] at h
  simp [
    AndAnd__Not.equ.False true,
    AndAnd__Not.equ.False false
  ] at h


-- created on 2024-07-01
