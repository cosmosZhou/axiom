import Axiom.Algebra.Pow_Add.eq.MulPowS
open Algebra


@[main]
private lemma main
  [Monoid M]
  {a : M}
  {m n : ℕ} :
-- imply
  a ^ m * a ^ n = a ^ (m + n) :=
-- proof
  Pow_Add.eq.MulPowS.symm


-- created on 2025-03-15
