import sympy.polys.domains
import Axiom.Basic
open Algebra


@[main]
private lemma main
  [IntegerRing α]
  {a b : α}
-- given
  (h : a > b) :
-- imply
  a - 1 ≥ b :=
-- proof
  IntegerRing.le_pred_of_lt h


-- created on 2024-07-01
