import Lemma.Algebra.Sub.ge.Zero.is.Le
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
  Sub.ge.Zero.is.Le.mpr h


-- created on 2024-11-25
