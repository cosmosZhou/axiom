import Axiom.Algebra.Ne_Sub.of.NeAdd
open Algebra


@[main]
private lemma main
  [AddGroup α]
  {x a b: α}
-- given
  (h : a ≠ x + b) :
-- imply
  a - b ≠ x :=
-- proof
  (Ne_Sub.of.NeAdd h.symm).symm


-- created on 2024-11-27
