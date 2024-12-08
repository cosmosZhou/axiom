import Axiom.Basic


namespace Algebra.And.to

theorem Cond
-- given
  (h : p ∧ q)
  (left : Bool := true) :
-- imply
  match left with
  | true => p
  | false => q := by
-- proof
  cases left
  case true =>
    exact h.left
  case false =>
    exact h.right


end Algebra.And.to

-- created on 2024-07-01
