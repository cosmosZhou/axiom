import Lemma.Algebra.Gt.is.False.of.Lt
open Algebra


@[main]
private lemma main
  [PartialOrder α]
  {a b : α}
-- given
  (h : a > b) :
-- imply
  a < b ↔ False := by
-- proof
  apply Gt.is.False.of.Lt h


-- created on 2025-03-29
