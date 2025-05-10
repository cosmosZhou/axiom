import Lemma.Algebra.EqFloor.is.Le.et.Lt
import Lemma.Algebra.Div.ge.FDiv
import Lemma.Algebra.Div.lt.Add1FDiv
import Lemma.Algebra.Add.comm
open Algebra


@[main]
private lemma main
  {n d : ℤ} :
-- imply
  n // d = ⌊n / (d : ℚ)⌋ := by
-- proof
  apply Eq.symm
  rw [EqFloor.is.Le.et.Lt]
  constructor
  apply Div.ge.FDiv
  rw [Add.comm]
  apply Div.lt.Add1FDiv


-- created on 2025-03-21
-- updated on 2025-03-28
