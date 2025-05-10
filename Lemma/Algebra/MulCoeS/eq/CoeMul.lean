import Lemma.Algebra.CoeMul.eq.MulCoeS
open Algebra


@[main]
private lemma nat
  [NonAssocSemiring α]
  {a b : ℕ} :
-- imply
  a * b = ((a * b : ℕ) : α) :=
-- proof
  CoeMul.eq.MulCoeS.nat.symm


@[main]
private lemma main
  [NonAssocRing α]
  {a b : ℤ} :
-- imply
  a * b = ((a * b : ℤ) : α) :=
-- proof
  CoeMul.eq.MulCoeS.symm


-- created on 2025-05-04
