import Lemma.Algebra.AddCeil.eq.CeilAdd
import Lemma.Algebra.AddSub.eq.Add_Sub
import Lemma.Algebra.EqAddS.of.Eq
import Lemma.Logic.Exist_Eq.of.IsOdd
import Lemma.Algebra.DivAdd.eq.AddDivS
import Lemma.Algebra.Add_Add.eq.AddAdd
import Lemma.Logic.EqFunS.of.Eq
open Algebra Logic


@[main]
private lemma main
  [LinearOrderedField α]
  [FloorRing α]
  {x : α}
  {n : ℤ}
-- given
  (h : n is odd) :
-- imply
  ⌈x + n / 2⌉ = ⌈x - 1 / 2⌉ + (n + 1) / 2 := by
-- proof
  rw [AddCeil.eq.CeilAdd]
  apply EqFunS.of.Eq
  rw [AddSub.eq.Add_Sub]
  apply EqAddS.of.Eq.left
  have := Exist_Eq.of.IsOdd h
  let ⟨k, hk⟩ := this
  rw [hk]
  simp
  rw [DivAdd.eq.AddDivS]
  simp
  ring_nf
  simp
  rw [DivAdd.eq.AddDivS]
  norm_num
  rw [Add_Add.eq.AddAdd]
  apply EqAddS.of.Eq (d := (k : α))
  norm_num


-- created on 2025-03-04
-- updated on 2025-04-26
