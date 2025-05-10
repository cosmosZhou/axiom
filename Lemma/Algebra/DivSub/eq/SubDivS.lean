import Lemma.Algebra.DivAdd.eq.AddDivS
import Lemma.Algebra.Add_Neg.eq.Sub
import Lemma.Algebra.DivNeg.eq.NegDiv
open Algebra


@[main]
private lemma main
  [Field α]
  {x y a : α} :
-- imply
  (x - y) / a = x / a - y / a := by
-- proof
  have := DivAdd.eq.AddDivS (x := x) (y := -y) (a := a)
  rw [DivNeg.eq.NegDiv] at this
  simp [Add_Neg.eq.Sub] at this
  assumption


-- created on 2025-03-02
