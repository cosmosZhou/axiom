import Axiom.Algebra.CoeAdd.eq.AddCoeS
open Algebra


@[main]
private lemma nat
  [AddGroupWithOne α]
  {a b : ℕ} :
-- imply
  a + b = ((a + b : ℕ) : α) := by
-- proof
  rw [CoeAdd.eq.AddCoeS.nat]


/--
This lemma ensures that adding two integers `a` and `b` and then casting the result to a type `α` with an additive group structure is equivalent to casting each integer to `α` first and then adding them within `α`.
This coherence between integer addition and coercion is vital for maintaining algebraic consistency across types with compatible structures.
-/
@[main]
private lemma int
  [AddGroupWithOne α]
  {a b : ℤ} :
-- imply
  a + b = ((a + b : ℤ) : α) := by
-- proof
  rw [CoeAdd.eq.AddCoeS.int]


@[main]
private lemma main
  [DivisionRing α]
  [CharZero α]
  {a b : ℚ} :
-- imply
  (a + b : α) = ↑(a + b) := by
-- proof
  rw [CoeAdd.eq.AddCoeS]


-- created on 2025-04-04
-- updated on 2025-04-20
