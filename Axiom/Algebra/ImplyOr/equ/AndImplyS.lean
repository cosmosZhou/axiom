import Axiom.Algebra.Imply.equ.OrNot
import Axiom.Algebra.And_Or.equ.OrAndS
import Axiom.Algebra.AndOr.equ.OrAndS
import Axiom.Algebra.OrOr.equ.Or_Or
import Axiom.Algebra.OrAnd.equ.AndOrS
import Axiom.Algebra.OrAndS.equ.AndOr
import Axiom.Algebra.Or_Or.equ.OrOr
import Axiom.Algebra.AndOr.equ.Cond
open Algebra


@[main]
private lemma main :
-- imply
  (p ∨ q) → r ↔ (p → r) ∧ (q → r)  := by
-- proof
  rw [Imply.equ.OrNot]
  rw [Imply.equ.OrNot]
  rw [Imply.equ.OrNot]
  rw [And_Or.equ.OrAndS]
  simp
  rw [AndOr.equ.OrAndS]
  rw [AndOr.equ.OrAndS]
  simp
  rw [OrOr.equ.Or_Or]
  rw [OrAnd.equ.AndOrS (q := r)]
  simp [OrAndS.equ.AndOr false]
  rw [Or_Or.equ.OrOr]
  simp [AndOr.equ.Cond true]


-- created on 2024-07-01
