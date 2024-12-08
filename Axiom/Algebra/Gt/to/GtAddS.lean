import Axiom.Algebra.Lt.to.LtAddS

namespace Algebra.Gt.to

theorem GtAddS
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
    Lt.to.LtAddS h a true
  | false =>
    Lt.to.LtAddS h a


end Algebra.Gt.to

-- created on 2024-07-01
