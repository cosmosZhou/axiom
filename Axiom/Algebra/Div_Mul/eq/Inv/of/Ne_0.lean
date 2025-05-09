import Axiom.Algebra.Div_Mul.eq.DivDiv
import Axiom.Algebra.Mul.comm
open Algebra


private lemma inv'
  [Field α]
  {a b : α}
-- given
  (h : a ≠ 0) :
-- imply
  a / (a * b) = b⁻¹ := by
-- proof
  rw [Div_Mul.eq.DivDiv]
  simp [h]

/--
open namespace in
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
  | true =>
    a / (b * a) = b⁻¹
  | false =>
    a / (a * b) = b⁻¹ := by
-- proof
  match comm with
  | true =>
    simp
    rw [Mul.comm]
    apply inv' h
  | false =>
    simp
    apply inv' h


-- created on 2024-07-01
-- updated on 2025-04-07
