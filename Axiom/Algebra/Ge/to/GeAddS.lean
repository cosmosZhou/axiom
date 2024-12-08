import Axiom.Algebra.Le.to.LeAddS

namespace Algebra.Ge.to

theorem GeAddS
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
    Le.to.LeAddS h a true
  | false =>
    Le.to.LeAddS h a


end Algebra.Ge.to

-- created on 2024-07-01
