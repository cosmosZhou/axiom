import Axiom.Basic


@[simp, main]
private lemma main
  [Field α]
  {a b : α}
-- given
  (h : a ≠ 0)
  (comm : Bool := false):
-- imply
  match comm with
    | true => a * b / a = b
    | false => b * a / a = b := by
-- proof
  cases comm <;>
  ·
    simp [h]


-- created on 2024-07-01
