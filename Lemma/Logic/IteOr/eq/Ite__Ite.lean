import Lemma.Logic.Ite__Ite.eq.IteOr
open Logic


@[main]
private lemma main
  [Decidable p]
  [Decidable q]
  {a b : α} :
-- imply
  (if p ∨ q then
    a
  else
    b) = if p then
    a
  else if q then
    a
  else
    b :=
-- proof
  Ite__Ite.eq.IteOr.symm


-- created on 2025-04-28
