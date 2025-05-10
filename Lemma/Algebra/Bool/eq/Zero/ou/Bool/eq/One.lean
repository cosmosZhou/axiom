import sympy.core.power
import Lemma.Set.Bool.in.Finset
import Lemma.Set.OrEqS.of.Mem_Finset
open Set


@[main]
private lemma main
  [Decidable p] :
-- imply
  Bool.toNat p = 0 ∨ Bool.toNat p = 1 := by
-- proof
  have := Bool.in.Finset (p := p)
  exact OrEqS.of.Mem_Finset this


-- created on 2025-04-20
