import Axiom.Algebra.EqSubS.of.Eq
import Axiom.Algebra.EqSubAdd
open Algebra


@[main]
private lemma main
  [AddGroup α]
  {x y : α}
-- given
  (h : x ≠ y)
  (d : α)
  (left : Bool := false) :
-- imply
  match left with
  | true => d + x ≠ d + y
  | false => x + d ≠ y + d := by
-- proof
  cases left with
  | true =>
    intro h'
    have h' := EqSubS.of.Eq h' d
    simp at h'
    exact h h'
  | false =>
    intro h'
    have h' := EqSubS.of.Eq h' d
    simp only [EqSubAdd.right] at h'
    exact h h'


-- created on 2024-11-27
