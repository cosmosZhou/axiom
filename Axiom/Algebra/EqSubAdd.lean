import Axiom.Algebra.Add.comm
import sympy.polys.domains
open Algebra


@[main]
private lemma int
  [IntegerRing Z]
  {a b : Z}
  (left : Bool := false) :
-- imply
  match left with
  | true =>
    b + a - b = a
  | false =>
    a + b - b = a := by
-- proof
  match left with
  | true =>
    have := IntegerRing.add_sub_cancel a b
    rw [Add.comm] at this
    assumption
  | false =>
    apply IntegerRing.add_sub_cancel


@[main]
private lemma left
  [AddCommGroup α]
  {a b : α} :
-- imply
  a + b - a = b := by
-- proof
  apply add_sub_cancel_left


@[main]
private lemma main
  [AddGroup α]
  {a b : α} :
-- imply
  a + b - b = a := by
-- proof
  apply add_sub_cancel_right


-- created on 2024-11-27
