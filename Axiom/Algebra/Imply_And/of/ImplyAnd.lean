import Axiom.Basic
open Algebra


@[main]
private lemma main
  {p q r: Prop}
-- given
  (h : p ∧ q → r)
  (left : Bool := true) :
-- imply
  match left with
  | true => p ∧ q → p ∧ r
  | false => p ∧ q → q ∧ r :=
-- proof
  match left with
  | true =>
    fun h_pq =>
      ⟨h_pq.left, h h_pq⟩
  | false =>
    fun h_pq =>
      ⟨h_pq.right, h h_pq⟩


-- created on 2025-01-12
