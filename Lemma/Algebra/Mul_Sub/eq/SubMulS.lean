import Lemma.Algebra.SubMulS.eq.Mul_Sub
open Algebra


@[main]
private lemma nat
  {x a b : ℕ} :
-- imply
  x * (a - b) = x * a - x * b := by
-- proof
  rw [SubMulS.eq.Mul_Sub.nat]


@[main]
private lemma main
  [NonUnitalNonAssocRing α]
  {x a b : α} :
-- imply
  x * (a - b) = x * a - x * b := by
-- proof
  rw [SubMulS.eq.Mul_Sub]


-- created on 2024-07-01
-- updated on 2025-03-31
