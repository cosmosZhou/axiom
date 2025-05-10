import Lemma.Algebra.Div.eq.Mul_Inv
open Algebra


/--
This lemma establishes the equivalence between multiplication by the inverse and division in a `DivInvMonoid`, serving as the reverse of `Div.eq.Mul_Inv`.
It simplifies expressions by allowing the interchange of `a * b⁻¹` and `a / b` within the algebraic structure `α`.
-/
@[main]
private lemma main
  [DivInvMonoid α]
  {a b : α} :
-- imply
  a * b⁻¹ = a / b := by
-- proof
  rw [Div.eq.Mul_Inv]


-- created on 2024-07-01
-- updated on 2025-04-04
