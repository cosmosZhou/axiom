import sympy.core.logic
import sympy.core.relational
import Axiom.Algebra.Eq_Neg.of.EqNeg
import Axiom.Logic.Cond_Ite.of.OrAndS
import Axiom.Logic.OrAndS.of.Cond_Ite
import Axiom.Algebra.EqNeg.of.Eq_Neg
open Algebra Logic


@[main]
private lemma main
  [Decidable p]
  [InvolutiveNeg α]
  {a b : α} :
-- imply
  (if p then
    -a
  else
    -b) = -if p then
    a
  else
    b := by
-- proof
  denote h_I : I = left
  have := OrAndS.of.Cond_Ite h_I
  mp [EqNeg.of.Eq_Neg (a := I) (b := a)] at this
  mp [EqNeg.of.Eq_Neg (a := I) (b := b)] at this
  rw [← h_I]
  apply Eq_Neg.of.EqNeg
  apply Cond_Ite.of.OrAndS
  assumption


-- created on 2025-04-26
