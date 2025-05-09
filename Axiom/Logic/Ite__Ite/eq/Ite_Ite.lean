import Axiom.Logic.Ite_Ite.eq.Ite__Ite
open Logic


@[main]
private lemma main
  [Decidable p]
  [Decidable q]
  {a b c : α} :
-- imply
  (if p ∧ q then
    a
  else if p then
    b
  else
    c) = (if p then
  (if q then
      a
    else
      b)
  else
    c) := 
-- proof
  Ite_Ite.eq.Ite__Ite.symm


-- created on 2025-04-18
