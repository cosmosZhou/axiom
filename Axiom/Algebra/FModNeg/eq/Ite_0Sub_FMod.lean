import sympy.core.relational
import Axiom.Algebra.Any_Eq_Mul.of.FMod.eq.Zero
import Axiom.Algebra.EqNegS.of.Eq
import Axiom.Algebra.NegMul.eq.MulNeg
import Axiom.Algebra.FMod.eq.Zero.of.Any_Eq_Mul
import Axiom.Algebra.Any_Eq_AddMul.of.EqFMod
import Axiom.Logic.Ne.of.NotEq
import Axiom.Algebra.FMod.eq.Sub_MulFDiv
import Axiom.Algebra.FDiv.eq.FloorDiv
import Axiom.Algebra.NegAdd.eq.SubNeg
import Axiom.Algebra.CoeSub.eq.SubCoeS
import Axiom.Algebra.DivSub.eq.SubDivS
import Axiom.Algebra.EqDivMul.of.Ne_0
import Axiom.Algebra.NeCoeS.of.Ne
import Axiom.Algebra.Sub.eq.Add_Neg
import Axiom.Algebra.FloorAdd.eq.Add_Floor
import Axiom.Algebra.MulAdd.eq.AddMulS
import Axiom.Algebra.Sub_Add.eq.SubSub
import Axiom.Algebra.EqSubS.of.Eq
import Axiom.Algebra.NegDiv.eq.DivNeg
import Axiom.Algebra.FDivNegFMod.eq.Neg1.of.FMod.ne.Zero.Ne_0
import Axiom.Algebra.DivInt.eq.Div
import Axiom.Algebra.FloorDiv.eq.FDiv
open Algebra Logic


@[main]
private lemma main
  {n d : ℤ} :
-- imply
  (-n).fmod d =
    if n.fmod d = 0 then
      0
    else
      d - n.fmod d := by
-- proof
  split_ifs with h
  ·
    have := Any_Eq_Mul.of.FMod.eq.Zero h
    let ⟨k, h⟩ := this
    have := EqNegS.of.Eq h
    rw [NegMul.eq.MulNeg] at this
    have : ∃ k, -n = k * d := by 
      use -k
    apply FMod.eq.Zero.of.Any_Eq_Mul this
  ·
    denote h_r : n.fmod d = r
    have h_Any := Any_Eq_AddMul.of.EqFMod h_r
    let ⟨q, h_Eq⟩ := h_Any
    rw [h_r] at h
    have h := Ne.of.NotEq h
    rw [h_r]
    rw [FMod.eq.Sub_MulFDiv]
    rw [h_Eq]
    rw [FDiv.eq.FloorDiv]
    rw [NegAdd.eq.SubNeg]
    rw [CoeSub.eq.SubCoeS.int]
    rw [DivSub.eq.SubDivS]
    simp
    by_cases h_d : d = 0
    ·
      simp_all [h_d]
    ·
      have h_d := Ne.of.NotEq h_d
      rw [NegMul.eq.MulNeg (b := (d : ℚ))]
      rw [EqDivMul.of.Ne_0 (NeCoeS.of.Ne h_d)]
      rw [Sub.eq.Add_Neg (a := -(q : ℚ))]
      norm_cast
      rw [FloorAdd.eq.Add_Floor]
      rw [MulAdd.eq.AddMulS]
      rw [Sub_Add.eq.SubSub]
      ring_nf
      apply EqSubS.of.Eq
      simp [NegDiv.eq.DivNeg]
      rw [DivInt.eq.Div]
      rw [FloorDiv.eq.FDiv]
      rw [← h_r]
      rw [← h_r] at h
      have h_Eq := FDivNegFMod.eq.Neg1.of.FMod.ne.Zero.Ne_0 h h_d
      rw [h_Eq]
      ring


-- created on 2025-03-30
-- updated on 2025-05-04
