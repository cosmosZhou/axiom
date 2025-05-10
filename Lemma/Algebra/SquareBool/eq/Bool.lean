import sympy.core.power
import Lemma.Algebra.Bool.eq.SquareBool
open Algebra


@[main]
private lemma main
  [Decidable p] :
-- imply
  (Bool.toNat p)² = Bool.toNat p :=
-- proof
  Bool.eq.SquareBool (p := p).symm


-- created on 2025-04-20
