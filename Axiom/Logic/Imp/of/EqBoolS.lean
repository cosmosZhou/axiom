import Axiom.Algebra.EqMulS.of.Eq
import Axiom.Algebra.SquareBool.eq.Bool
import Axiom.Algebra.Mul.eq.Square
import Axiom.Logic.Imp.of.Bool.eq.MulBoolS
open Algebra Logic


@[main]
private lemma main
  [Decidable p]
  [Decidable q]
-- given
  (h : Bool.toNat p = Bool.toNat q) :
-- imply
  p → q := by
-- proof
  have := EqMulS.of.Eq.left h (Bool.toNat p)
  rw [Mul.eq.Square] at this
  rw [SquareBool.eq.Bool] at this
  exact Imp.of.Bool.eq.MulBoolS this


-- created on 2025-04-20
