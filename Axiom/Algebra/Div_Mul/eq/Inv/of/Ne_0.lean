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


@[main]
private lemma main
  [Field α]
  {a b : α}
-- given
  (h : a ≠ 0)
  (comm : Bool := false) :
-- imply
  match comm with
  | true  =>
    a / (b * a) = b⁻¹
  | false =>
    a / (a * b) = b⁻¹ := by
-- proof
  cases comm with
  | true  =>
    simp
    rw [Mul.comm]
    apply inv' h
  | false =>
    simp
    apply inv' h


-- created on 2024-07-01
