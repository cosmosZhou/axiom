import Axiom.Algebra.LeAddS.of.Le
open Algebra


@[main]
private lemma main
  -- [OrderedAddCommGroup α]
  [Add α] [LE α]
  [AddLeftMono α]
  [AddRightMono α]

  {b c : α}
-- given
  (h : b ≥ c)
  (a : α)
  (left : Bool := false) :
-- imply
  match left with
  | true =>
    a + b ≥ a + c
  | false =>
    b + a ≥ c + a :=
-- proof
  match left with
  | true =>
    LeAddS.of.Le h a true
  | false =>
    LeAddS.of.Le h a


-- created on 2024-07-01
