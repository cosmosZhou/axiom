import Lemma.Algebra.NotGt.of.Lt
open Algebra


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h : a > b) :
-- imply
  ¬a < b :=
-- proof
  NotGt.of.Lt h


-- created on 2025-03-30
