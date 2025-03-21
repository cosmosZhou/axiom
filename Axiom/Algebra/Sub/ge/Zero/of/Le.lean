import Axiom.Algebra.GeSub__0.equ.Le
open Algebra


@[main]
private lemma main
  [AddGroup α] [LE α] [AddRightMono α]
  {a b : α}
-- given
  (h : a ≤ b) :
-- imply
  b - a ≥ 0 :=
-- proof
  GeSub__0.equ.Le.mpr h


-- created on 2024-11-25
