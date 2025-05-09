import Axiom.Algebra.NotGe.of.Lt
import Axiom.Logic.Iff_False.of.Not
open Algebra Logic


@[main]
private lemma main
  [PartialOrder α]
  {a b : α}
-- given
  (h : a < b) :
-- imply
  a ≥ b ↔ False := by
-- proof
  have := NotGe.of.Lt h
  apply Iff_False.of.Not this


-- created on 2025-03-29
