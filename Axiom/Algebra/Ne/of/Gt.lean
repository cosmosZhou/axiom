import Axiom.Algebra.Ne.of.Lt
open Algebra


@[main]
private lemma main
  [Preorder α]
  {x y : α}
-- given
  (h : x > y) :
-- imply
  x ≠ y :=
  (Ne.of.Lt h).symm


-- created on 2024-07-01
