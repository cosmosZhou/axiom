import Axiom.Algebra.NotLt.of.Ge
open Algebra


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h : a ≤ b) :
-- imply
  ¬a > b := by
-- proof
  apply NotLt.of.Ge h


-- created on 2025-03-29
-- updated on 2025-03-30
