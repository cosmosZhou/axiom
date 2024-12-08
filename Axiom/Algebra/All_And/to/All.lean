import Axiom.Basic


namespace Algebra.All_And.to

theorem All
  {p q : α → Prop}
-- given
  (h : ∀ x : α, p x ∧ q x)
  (left : Bool := true) :
-- imply
  match left with
  | true =>
    ∀ x : α, p x
  | false =>
    ∀ x : α, q x := by

-- proof
  cases left
  case true =>
    intro x
    exact (h x).left
  case false =>
    intro x
    exact (h x).right


end Algebra.All_And.to

-- created on 2024-07-01
