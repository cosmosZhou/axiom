import Axiom.Algebra.LtAddS.of.Lt
open Algebra


@[main]
private lemma main
  -- [OrderedAddCommGroup α]
  [Add α]
  [LT α]
  [AddLeftStrictMono α]
  [AddRightStrictMono α]
  {b c : α}
-- given
  (h : b > c)
  (a : α)
  (left: Bool := false) :
-- imply
  match left with
  | true =>
    a + b > a + c
  | false =>
    b + a > c + a :=
-- proof
  match left with
  | true =>
    LtAddS.of.Lt h a true
  | false =>
    LtAddS.of.Lt h a


-- created on 2024-07-01
