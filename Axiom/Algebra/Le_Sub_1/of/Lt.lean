import sympy.polys.domains
import Axiom.Basic


@[main]
private lemma main
  [IntegerRing α]
  {a b : α}
-- given
  (h : a < b) :
-- imply
  a ≤ b - 1 :=
-- proof
  IntegerRing.le_pred_of_lt h


-- created on 2024-07-01
