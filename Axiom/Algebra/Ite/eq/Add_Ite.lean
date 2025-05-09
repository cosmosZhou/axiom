import sympy.core.relational
import Axiom.Logic.CondIte.of.OrAndS
import Axiom.Logic.OrAndS.of.Cond_Ite
import Axiom.Algebra.EqSub.of.Eq_Add
import Axiom.Algebra.EqSub.is.Eq_Add
import Axiom.Algebra.Add.comm
open Logic Algebra


@[main]
private lemma main
  [Decidable p]
  [AddCommGroup α]
  {a b c : α} :
-- imply
  (if p then
    c + a
  else
    c + b) = c + if p then
    a
  else
    b := by
-- proof
  denote h_Ite : I = right
  have := EqSub.of.Eq_Add.left h_Ite
  have := OrAndS.of.Cond_Ite this
  rw [EqSub.is.Eq_Add] at this
  rw [EqSub.is.Eq_Add] at this
  rw [Eq.comm] at this
  rw [Eq.comm (a := I)] at this
  rw [Add.comm] at this
  rw [Add.comm (a := b)] at this
  rw [← h_Ite]
  apply CondIte.of.OrAndS
  assumption


-- created on 2025-04-26
