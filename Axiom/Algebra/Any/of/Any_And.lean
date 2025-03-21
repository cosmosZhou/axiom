import Axiom.Basic


@[main]
private lemma main
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
  cases left with
  | true =>
    exact ⟨x, hLeft⟩
  | false =>
    exact ⟨x, hRight⟩


-- created on 2024-07-01
