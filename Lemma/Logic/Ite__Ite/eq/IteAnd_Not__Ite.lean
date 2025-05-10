import sympy.core.relational
import Lemma.Logic.And.ou.OrAndS.of.Cond_Ite__Ite
import Lemma.Logic.And_NotAnd_Not.is.OrAndS
import Lemma.Logic.And_And.is.And.of.Imp
import Lemma.Logic.IffOrAndS
import Lemma.Logic.Or_Or.is.OrOr
import Lemma.Logic.OrOr.comm
import Lemma.Logic.OrOr.is.Or_Or
import Lemma.Logic.Cond_Ite__Ite.is.And.ou.OrAndS
import Lemma.Logic.Imp.et.Not.is.NotOr
open Logic


@[main]
private lemma main
  [Decidable p]
  [Decidable q]
  {a b c : α} :
-- imply
  (if p then
    a
  else if q then
    b
  else
    c) = if q ∧ ¬p then
    b
  else if p then
    a
  else
    c := by
-- proof
  denote h_Q : Q = right
  have := And.ou.OrAndS.of.Cond_Ite__Ite h_Q
  rw [And_NotAnd_Not.is.OrAndS] at this
  simp at this
  rw [And_And.is.And.of.Imp (by simp : p → p) q] at this
  rw [IffOrAndS] at this
  rw [Or_Or.is.OrOr] at this
  rw [OrOr.comm] at this
  rw [OrOr.is.Or_Or] at this
  rw [Imp.et.Not.is.NotOr] at this
  rw [← h_Q]
  apply Eq.symm
  rw [Cond_Ite__Ite.is.And.ou.OrAndS (R := Eq)]
  assumption


-- created on 2025-04-09
-- updated on 2025-04-11
