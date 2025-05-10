import Lemma.Basic


/--
This lemma asserts the commutativity of the multiplication operation in a commutative magma.
Specifically, for any elements `a` and `b` in the magma, the product `a * b` is equal to `b * a`, as established by the underlying commutative property of the magma's binary operation.
-/
@[main]
private lemma main
  [CommMagma α]
  {a b : α} :
-- imply
  a * b = b * a := by
-- proof
  apply mul_comm


-- created on 2024-07-01
-- updated on 2025-04-04
