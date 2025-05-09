import sympy.core.relational
import Axiom.Logic.Cond_Ite.of.OrAndS
import Axiom.Logic.IffNotNot
import Axiom.Logic.OrAndS.of.Cond_Ite
open Logic


@[main]
private lemma main
  [Decidable p]
  {a b : α} :
-- imply
  (if p then
    a
  else
    b) = if ¬p then
    b
  else
    a := by
-- proof
  denote h_P : P = left
  have := OrAndS.of.Cond_Ite h_P
  rw [← h_P]
  apply Cond_Ite.of.OrAndS
  rw [IffNotNot]
  rw [Or.comm]
  assumption


-- created on 2025-04-17
