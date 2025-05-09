import sympy.core.power
import Axiom.Algebra.Bool.eq.SquareBool
open Algebra


@[main]
private lemma main
  [Decidable p] :
-- imply
  (Bool.toNat p)² = Bool.toNat p :=
-- proof
  Bool.eq.SquareBool (p := p).symm


-- created on 2025-04-20
