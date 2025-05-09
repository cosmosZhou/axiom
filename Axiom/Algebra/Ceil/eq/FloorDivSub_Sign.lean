import Axiom.Algebra.Ceil.eq.Neg.Floor
import Axiom.Algebra.DivSub.eq.SubDivS
import Axiom.Algebra.DivAdd.eq.AddDivS
import Axiom.Algebra.Div.eq.One.of.Ne_0
import Axiom.Algebra.SubAdd.eq.Add_Sub
import Axiom.Algebra.Eq_Add.of.EqSub
import Axiom.Algebra.Eq.of.EqNegS
import Axiom.Algebra.NegSub.eq.Sub
import Axiom.Algebra.Sub_Neg.eq.Add
import Axiom.Algebra.EqAddS.of.Eq.Eq
import Axiom.Algebra.FloorAdd1.eq.Add1Floor
import Axiom.Algebra.FMod.eq.Sub_MulFDiv
import Axiom.Algebra.FDivAdd.eq.Add1FDiv.of.Ne_0
import Axiom.Algebra.MulAdd.eq.AddMulS
import Axiom.Algebra.FModAdd.eq.FMod
import Axiom.Algebra.Add_Sub.eq.SubAdd
import Axiom.Algebra.Add_Neg.eq.Sub
import Axiom.Algebra.AddFModS.eq.FModNegSign
import Axiom.Algebra.FModNegSign.eq.Sub_Sign
import Axiom.Algebra.SubNeg.comm
import Axiom.Algebra.SubSub.eq.Sub_Add
import Axiom.Algebra.Add.comm
import Axiom.Algebra.Sub_Add.eq.SubSub
import Axiom.Algebra.Eq.of.EqSubS
import Axiom.Algebra.Mul.comm
import Axiom.Algebra.EqNegS.of.Eq
import Axiom.Algebra.EqAddS.of.Eq
import Axiom.Algebra.AddMul.eq.MulAdd_1
import Axiom.Logic.Ne.of.NotEq
import Axiom.Algebra.Eq_0.of.Mul.eq.Zero.Ne_0
import Axiom.Algebra.Eq_Neg.of.Add.eq.Zero
import Axiom.Algebra.FDiv.eq.FloorDiv
import Axiom.Algebra.CoeNeg.eq.NegCoe
import Axiom.Algebra.DivNeg.eq.NegDiv
open Algebra Logic


/--
This lemma establishes an equivalence between the ceiling of the division of two integers and the floor of an adjusted division expression. 
Specifically, for integers `n` and `d`, the ceiling of `n / d` is equal to the floor of `(d + n - sign(d)) / d`. 
This relationship leverages properties of the ceiling and floor functions, along with the sign of the divisor `d`, to transform the ceiling operation into a floor operation with a modified numerator. 
The proof involves case analysis on whether `d` is zero and utilizes algebraic manipulations and properties of integer division to achieve the equivalence.
-/
@[main]
private lemma main
  {n d : ℤ} :
-- imply
  ⌈n / (d : ℚ)⌉ = ⌊(d + n - sign d) / (d : ℚ)⌋ := by
-- proof
  by_cases h : (d : ℚ) = 0
  ·
    rw [h]
    norm_num
  ·
    rw [Ceil.eq.Neg.Floor]
    rw [DivSub.eq.SubDivS]
    rw [DivAdd.eq.AddDivS]
    rw [Div.eq.One.of.Ne_0 h]
    rw [SubAdd.eq.Add_Sub]
    rw [← DivSub.eq.SubDivS]
    norm_cast
    rw [FloorAdd1.eq.Add1Floor]
    apply Eq_Add.of.EqSub
    apply Eq.of.EqNegS
    rw [NegSub.eq.Sub]
    rw [Sub_Neg.eq.Add]
    have h₀ := FMod.eq.Sub_MulFDiv (n := -n) (d := d)
    have h₁ := FMod.eq.Sub_MulFDiv (n := (d + n - sign (d))) (d := d)
    rw [SubAdd.eq.Add_Sub] at h₁
    norm_cast at h
    have h := Ne.of.NotEq h
    rw [FDivAdd.eq.Add1FDiv.of.Ne_0 h] at h₁
    rw [MulAdd.eq.AddMulS] at h₁
    norm_num at h₁
    rw [FModAdd.eq.FMod] at h₁
    have := EqAddS.of.Eq.Eq h₀ h₁
    ring_nf at this
    rw [Add_Sub.eq.SubAdd] at this
    rw [Add_Neg.eq.Sub] at this
    rw [AddFModS.eq.FModNegSign] at this
    rw [FModNegSign.eq.Sub_Sign] at this
    rw [SubNeg.comm] at this
    rw [SubSub.eq.Sub_Add] at this
    rw [Add.comm] at this
    rw [Sub_Add.eq.SubSub] at this
    have := Eq.of.EqSubS this (sign d)
    rw [Mul.comm (a := d)] at this
    have := EqNegS.of.Eq this
    rw [NegSub.eq.Sub] at this
    rw [Sub_Neg.eq.Add] at this
    rw [← MulAdd.eq.AddMulS] at this
    have := EqAddS.of.Eq this d
    simp at this
    have := this.symm
    rw [AddMul.eq.MulAdd_1] at this
    have := Eq_0.of.Mul.eq.Zero.Ne_0 this h
    have := Eq_Neg.of.Add.eq.Zero this
    rw [FDiv.eq.FloorDiv] at this
    rw [FDiv.eq.FloorDiv] at this
    rw [CoeNeg.eq.NegCoe] at this
    rw [DivNeg.eq.NegDiv] at this
    norm_cast at this


-- created on 2025-03-05
-- updated on 2025-04-04
