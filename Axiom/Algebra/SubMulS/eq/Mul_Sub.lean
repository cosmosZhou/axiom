import Axiom.Basic


@[main]
private lemma nat
  {x a b : ℕ} :
-- imply
  x * a - x * b = x * (a - b) := by
-- proof
  rw [Nat.mul_sub]


/--
This lemma demonstrates the distributive property of multiplication over subtraction in a non-unital, non-associative ring. 
Specifically, it shows that for any elements `x`, `a`, and `b` in such a ring, the expression `x * a - x * b` simplifies to `x * (a - b)`, even in the absence of multiplicative identity or associativity.
-/
@[main]
private lemma main
  [NonUnitalNonAssocRing α]
  {x a b : α} :
-- imply
  x * a - x * b = x * (a - b) := by
-- proof
  rw [mul_sub]


-- created on 2024-07-01
-- updated on 2025-04-04
