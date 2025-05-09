import Axiom.Algebra.FDiv.eq.Ite__Ite__Ite__Ite__Ite
import Axiom.Logic.Iff_True.of.Cond
import Axiom.Algebra.Lt.is.False.of.Gt
import Axiom.Algebra.Ge.is.True.of.Gt
import Axiom.Algebra.Eq.is.False.of.Gt
import Axiom.Algebra.Add_Neg.eq.Sub
import Axiom.Algebra.LeMulEDiv.of.Ge_0
import Axiom.Algebra.SubNeg.eq.NegAdd
import Axiom.Algebra.MulNeg.eq.NegMul
import Axiom.Algebra.LeNeg.of.Ge_Neg
import Axiom.Algebra.Neg.gt.Zero.of.Lt_0
import Axiom.Algebra.GeMulAdd1EDiv.of.Gt_0
open Algebra Logic


@[main]
private lemma main
  {d : ℤ}
-- given
  (h : d > 0)
  (n : ℤ) :
-- imply
  n // d * d ≤ n := by
-- proof
  rw [FDiv.eq.Ite__Ite__Ite__Ite__Ite]
  have := Iff_True.of.Cond h
  simp [this]
  have := Lt.is.False.of.Gt h
  simp [this]
  have := Ge.is.True.of.Gt h
  simp [this]
  have := Eq.is.False.of.Gt h
  simp [this]
  rw [Add_Neg.eq.Sub]
  split_ifs with h' h''
  ·
    apply LeMulEDiv.of.Ge_0 h' d
  ·
    rw [SubNeg.eq.NegAdd]
    rw [MulNeg.eq.NegMul]
    apply LeNeg.of.Ge_Neg
    apply GeMulAdd1EDiv.of.Gt_0 h
  ·
    linarith [h', h'']


-- created on 2025-03-29
