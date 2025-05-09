import Axiom.Logic.Iff_True.of.Cond
import Axiom.Algebra.Ge.of.Gt
open Algebra Logic


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h : a > b) :
-- imply
  a ≥ b ↔ True := by
-- proof
  have := Ge.of.Gt h
  apply Iff_True.of.Cond this


-- created on 2025-03-29
