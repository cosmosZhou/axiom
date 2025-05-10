import Lemma.Algebra.MulNeg.eq.NegMul
import Lemma.Algebra.Mul.eq.Square
open Algebra


@[main]
private lemma main
  [Ring α]
  {a : α} :
-- imply
  -a * a = -a² := by
-- proof
  rw [
    MulNeg.eq.NegMul,
    Mul.eq.Square
  ]


-- created on 2024-11-29
