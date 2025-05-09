import Axiom.Basic


/--
This lemma asserts that in a field, multiplying an element `b` by a non-zero element `a` and then dividing by `a` yields `b`, with the order of multiplication determined by the `comm` flag.
When `comm` is `true`, the multiplication is `a * b`, and when `false`, it is `b * a`, but in both cases, division by `a` cancels out the multiplication due to `a` being non-zero.
-/
@[main]
private lemma main
  [Field α]
  {a b : α}
-- given
  (h : a ≠ 0)
  (comm : Bool := false) :
-- imply
  match comm with
  | true => a * b / a = b
  | false => b * a / a = b := by
-- proof
  cases comm <;>
    simp [h]


-- created on 2024-07-01
-- updated on 2025-04-04
