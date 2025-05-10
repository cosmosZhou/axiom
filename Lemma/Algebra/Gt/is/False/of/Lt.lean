import Lemma.Algebra.Le.of.Lt
import Lemma.Algebra.NotGt.of.Le
import Lemma.Logic.Iff_False.of.Not
open Algebra Logic


@[main]
private lemma main
  [PartialOrder α]
  {a b : α}
-- given
  (h : a < b) :
-- imply
  a > b ↔ False := by
-- proof
  have := Le.of.Lt h
  have := NotGt.of.Le this
  apply Iff_False.of.Not this


-- created on 2025-03-27
-- updated on 2025-03-29
