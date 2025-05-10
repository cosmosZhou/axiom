import Lemma.Algebra.Any_Eq_Mul.of.FMod.eq.Zero
import Lemma.Algebra.EqNegS.of.Eq
import Lemma.Algebra.NegMul.eq.MulNeg
import Lemma.Algebra.FMod.eq.Zero.of.Any_Eq_Mul
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
