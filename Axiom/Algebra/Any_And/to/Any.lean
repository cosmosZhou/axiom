import Axiom.Basic


namespace Algebra.Any_And.to

theorem Any
  {p q : α → Prop}
-- given
  (h : ∃ x : α, p x ∧ q x)
  (left : Bool := true) :
-- imply
  match left with
  | true =>
    ∃ x : α, p x
  | false =>
    ∃ x : α, q x := by
-- proof
  let ⟨x, hLeft, hRight⟩ := h
  cases left
  case true =>
    exact ⟨x, hLeft⟩
  case false =>
    exact ⟨x, hRight⟩


end Algebra.Any_And.to

-- created on 2024-07-01
