import sympy.core.relational
import Axiom.Logic.Cond_Ite__Ite.is.And.ou.OrAndS
import Axiom.Logic.Or_Or.is.OrOr
import Axiom.Logic.OrAndS.is.And_Or
import Axiom.Logic.Or_And_Not.is.Or
import Axiom.Logic.Cond_Ite.is.OrAndS
import Axiom.Logic.NotOr.is.AndNotS
open Logic


@[main]
private lemma main
  [Decidable p]
  [Decidable q]
  {a b : α} :
-- imply
  (if p then
    a
  else if q then
    a
  else
    b) = if p ∨ q then
    a
  else
    b := by
-- proof
  denote h : R = right
  rw [← h]
  apply Eq.symm
  rw [Cond_Ite__Ite.is.And.ou.OrAndS (R := Eq)]
  rw [Or_Or.is.OrOr]
  simp [OrAndS.is.And_Or.left]
  rw [Or_And_Not.is.Or]
  rw [Cond_Ite.is.OrAndS (R := Eq)] at h
  rw [NotOr.is.AndNotS] at h
  assumption


-- created on 2025-04-18
-- updated on 2025-04-21
