import Axiom.Algebra.Ne.of.Lt
import Axiom.Algebra.Div.eq.One.of.Ne_0
open Algebra


@[main]
private lemma main
  [Preorder α]
  [GroupWithZero α]
  {x : α}
-- given
  (h : x < 0) :
-- imply
  x / x = 1 :=
-- proof
  (Div.eq.One.of.Ne_0 ∘ Ne.of.Lt) h


-- created on 2024-11-25
