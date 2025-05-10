import sympy.core.power
import Lemma.Algebra.Bool.eq.Zero.ou.Bool.eq.One
import Lemma.Algebra.Mul.eq.Zero.of.OrEqS
import Lemma.Algebra.AddNeg.eq.Sub
import Lemma.Algebra.Eq.of.Sub.eq.Zero
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
