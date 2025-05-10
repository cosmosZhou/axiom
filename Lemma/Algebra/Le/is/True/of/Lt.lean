import Lemma.Algebra.Le.of.Lt
import Lemma.Logic.Iff_True.of.Cond
open Algebra Logic


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h : a < b) :
-- imply
  a ≤ b ↔ True := by
-- proof
  have := Le.of.Lt h
  apply Iff_True.of.Cond this


-- created on 2025-03-29
