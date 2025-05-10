import Lemma.Logic.Cond_Ite.of.Imp.Imp
import Lemma.Algebra.FDiv.eq.EDiv.of.Ge_0
import Lemma.Logic.NotAnd.is.OrNotS
import Lemma.Algebra.NotGe.is.Lt
import Lemma.Logic.Eq_Ite.of.Cond.NotAnd.Eq
import Lemma.Logic.IffAndSAnd
import Lemma.Algebra.Gt.et.Lt.is.False
import Lemma.Logic.Iff_True.of.Cond
import Lemma.Algebra.Add_Neg.eq.Sub
import Lemma.Algebra.Eq.is.False.of.Lt
import Lemma.Algebra.Gt.is.False.of.Lt
import Lemma.Algebra.AddNeg.eq.Sub
import Lemma.Algebra.SubNeg.comm
import Lemma.Algebra.FDiv.eq.Ite.of.Lt_0
import Lemma.Algebra.FDiv.eq.Ite__Ite.of.Lt_0
open Logic Algebra


@[main]
private lemma main
  {n d : ℤ} :
-- imply
  n // d =
    if n ≥ 0 ∧ d ≥ 0 then
      n / d
    else if n > 0 ∧ d < 0 then
      -((n - 1) / -d + 1)
    else if n < 0 ∧ d = 0 then
      0
    else if n < 0 ∧ d > 0 then
      -((-n - 1) / d + 1)
    else
      -n / -d := by
-- proof
  apply Cond_Ite.of.Imp.Imp
  intro ⟨_, h⟩
  apply FDiv.eq.EDiv.of.Ge_0 (n := n) h
  rw [NotAnd.is.OrNotS]
  rw [NotGe.is.Lt, NotGe.is.Lt]
  intro h_Or
  cases h_Or with
  | inl h_Lt_0 =>
    apply Eq_Ite.of.Cond.NotAnd.Eq h_Lt_0
    rw [IffAndSAnd]
    rw [Gt.et.Lt.is.False]
    simp
    have := Iff_True.of.Cond h_Lt_0
    simp [this]
    rw [Add_Neg.eq.Sub]
    rw [SubNeg.comm]
    apply FDiv.eq.Ite__Ite.of.Lt_0 h_Lt_0
  | inr h_Lt_0 =>
    have := Iff_True.of.Cond h_Lt_0
    simp [this]
    have := Eq.is.False.of.Lt h_Lt_0
    simp [this]
    have := Gt.is.False.of.Lt h_Lt_0
    simp [this]
    rw [AddNeg.eq.Sub]
    apply FDiv.eq.Ite.of.Lt_0 h_Lt_0


-- created on 2025-03-21
-- updated on 2025-03-27
