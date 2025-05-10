import Lemma.Algebra.Lt.Ne.is.Lt
open Algebra


@[main]
private lemma main
  [Preorder α]
  {a b : α} :
-- imply
  a ≠ b ∧ a < b ↔ a < b := by
-- proof
  rw [And.comm]
  apply Lt.Ne.is.Lt


-- created on 2025-04-18
