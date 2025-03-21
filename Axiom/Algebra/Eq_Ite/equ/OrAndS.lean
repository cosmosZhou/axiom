import Axiom.Algebra.Eq_Ite.equ.AndImplyS_Eq
import Axiom.Algebra.Imply.equ.OrNot
import Axiom.Algebra.ImplyNot.equ.Or
import Axiom.Algebra.OrAndS.of.Or_Eq.Or_Eq
import Axiom.Algebra.Or_Eq.of.OrAndS
import Axiom.Algebra.OrNot_Eq.of.OrAndS
open Algebra


@[main]
private lemma main
  [Decidable p]
  {x a b: α} :
-- imply
  (x = if p then a else b) ↔
    x = a ∧ p ∨ x = b ∧ ¬p := by
-- proof
  rw [Eq_Ite.equ.AndImplyS_Eq]
  rw [Imply.equ.OrNot]
  rw [ImplyNot.equ.Or]
  constructor
  intro h
  apply OrAndS.of.Or_Eq.Or_Eq h.left h.right
  intro h
  exact And.intro (OrNot_Eq.of.OrAndS h) (Or_Eq.of.OrAndS h)


-- created on 2025-01-12
