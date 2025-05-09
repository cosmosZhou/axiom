import sympy.core.power
import Axiom.Algebra.Bool.eq.Zero.ou.Bool.eq.One
import Axiom.Algebra.Mul.eq.Zero.of.OrEqS
import Axiom.Algebra.AddNeg.eq.Sub
import Axiom.Algebra.Eq.of.Sub.eq.Zero
open Algebra


@[main]
private lemma main
  [Decidable p] :
-- imply
  Bool.toNat p = (Bool.toNat p)² := by
-- proof
  have := Bool.eq.Zero.ou.Bool.eq.One (p := p)
  have := Mul.eq.Zero.of.OrEqS.nat this
  ring_nf at this
  rw [AddNeg.eq.Sub] at this
  have := Eq.of.Sub.eq.Zero this
  norm_cast at this
  apply Eq.symm
  assumption


-- created on 2025-04-20
