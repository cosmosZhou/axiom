import Axiom.Algebra.Any_Eq_Mul.of.FMod.eq.Zero
import Axiom.Algebra.EqNegS.of.Eq
import Axiom.Algebra.NegMul.eq.MulNeg
import Axiom.Algebra.FMod.eq.Zero.of.Any_Eq_Mul
open Algebra


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : n.fmod d = 0) :
-- imply
  (-n).fmod d = 0 := by
-- proof
  have := Any_Eq_Mul.of.FMod.eq.Zero h
  let ⟨k, h_Eq⟩ := this
  have := EqNegS.of.Eq h_Eq
  rw [NegMul.eq.MulNeg] at this
  apply FMod.eq.Zero.of.Any_Eq_Mul
  use -k


-- created on 2025-03-30
