import sympy.core.logic
import Lemma.Logic.Bool.eq.One.of.Cond
import Lemma.Logic.Cond.of.Bool.eq.One
import Lemma.Logic.Imp.of.Imp.Imp
import Lemma.Logic.Or_Not.of.Imp
import Lemma.Logic.Bool.eq.Zero.of.Bool.ne.One
import Lemma.Algebra.Mul.eq.Zero.of.OrEqS
import Lemma.Algebra.MulSub.eq.SubMulS
import Lemma.Algebra.Eq.of.Sub.eq.Zero
import Lemma.Algebra.Mul.comm
import Lemma.Algebra.Eq.of.EqCoeS
open Logic Algebra


@[main]
private lemma main
  [Decidable p]
  [Decidable q]
-- given
  (h : p → q) :
-- imply
  Bool.toNat p = Bool.toNat p * Bool.toNat q := by
-- proof
  have h_P := Cond.of.Bool.eq.One (p := p)
  have h_Q := Bool.eq.One.of.Cond (p := q)
  have := Imp.of.Imp.Imp h h_Q
  have := Imp.of.Imp.Imp h_P this
  have := Or_Not.of.Imp this
  mp [Bool.eq.Zero.of.Bool.ne.One (p := p)] at this
  have := Mul.eq.Zero.of.OrEqS.nat this
  rw [MulSub.eq.SubMulS] at this
  simp at this
  have := Eq.of.Sub.eq.Zero this
  have := Eq.of.EqCoeS.nat this
  rw [Mul.comm]
  apply Eq.symm
  assumption


-- created on 2025-04-11
-- updated on 2025-04-18
