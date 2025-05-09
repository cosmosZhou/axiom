import Axiom.Algebra.Any_Eq_Mul.of.FMod.eq.Zero
import Axiom.Algebra.FMod.eq.Sub_MulFDiv
import Axiom.Algebra.Add.comm
import Axiom.Algebra.SubAdd.eq.Add_Sub
import Axiom.Algebra.Sub.eq.Add_Neg
import Axiom.Algebra.EqAddS.of.Eq
import Axiom.Algebra.FDiv.eq.FloorDiv
import Axiom.Algebra.CoeAdd.eq.AddCoeS
import Axiom.Algebra.DivAdd.eq.AddDivS
import Axiom.Algebra.CoeMul.eq.MulCoeS
import Axiom.Algebra.EqDivMul.of.Ne_0
import Axiom.Logic.Ne.of.NotEq
import Axiom.Algebra.NeCoeS.of.Ne
import Axiom.Algebra.FloorAdd.eq.AddFloor
import Axiom.Algebra.MulAdd.eq.AddMulS
import Axiom.Algebra.Sub_Add.eq.SubSub
import Axiom.Algebra.SubSub.eq.Neg
open Algebra Logic


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : n.fmod d = 0)
  (m : ℤ) :
-- imply
  (n + m).fmod d = m.fmod d := by
-- proof
  by_cases h_d : d = 0
  ·
    rw [h_d]
    norm_num
    rw [h_d] at h
    norm_num at h
    assumption
  ·
    have h_d := Ne.of.NotEq h_d
    have := Any_Eq_Mul.of.FMod.eq.Zero h
    let ⟨k, h_n⟩ := this
    rw [h_n]
    rw [FMod.eq.Sub_MulFDiv]
    rw [FMod.eq.Sub_MulFDiv]
    rw [Add.comm]
    rw [SubAdd.eq.Add_Sub]
    rw [Sub.eq.Add_Neg (a := m)]
    apply EqAddS.of.Eq.left
    rw [FDiv.eq.FloorDiv]
    rw [CoeAdd.eq.AddCoeS.int]
    rw [DivAdd.eq.AddDivS]
    rw [CoeMul.eq.MulCoeS]
    have := NeCoeS.of.Ne (R := ℚ) h_d
    rw [EqDivMul.of.Ne_0 this]
    rw [FloorAdd.eq.AddFloor]
    rw [MulAdd.eq.AddMulS]
    rw [Sub_Add.eq.SubSub]
    rw [SubSub.eq.Neg]
    rw [FDiv.eq.FloorDiv]


-- created on 2025-03-30
-- updated on 2025-04-26
