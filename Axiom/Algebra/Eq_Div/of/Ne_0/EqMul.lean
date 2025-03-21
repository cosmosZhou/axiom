import Axiom.Algebra.EqDivS.of.Eq
import Axiom.Algebra.EqDivMul.of.Ne_0
open Algebra


@[main]
private lemma main
  [Field α]
  {a c b : α}
  {left : Bool}
-- given
  (h_ne :
    match left with
    | true => a ≠ 0
    | false => b ≠ 0)
  (h : a * b = c) :
-- imply
  match left with
  | true => b = c / a
  | false => a = c / b := by
-- proof
  match left with
  | true =>
    have h := EqDivS.of.Eq h a
    have h_eq := EqDivMul.of.Ne_0 (b := b) h_ne true
    exact h_eq ▸ h
  | false =>
    have h := EqDivS.of.Eq h b
    have h_eq := EqDivMul.of.Ne_0 (b := a) h_ne
    exact h_eq ▸ h


-- created on 2024-07-01
-- updated on 2025-03-13
