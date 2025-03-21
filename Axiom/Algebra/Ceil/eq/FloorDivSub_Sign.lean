import Axiom.Algebra.Ceil.eq.Neg.Floor
import Axiom.Algebra.DivSub.eq.SubDivS
import Axiom.Algebra.DivAdd.eq.AddDivS
import Axiom.Algebra.Div.eq.One.of.Ne_0
import Axiom.Algebra.SubAdd.eq.Add_Sub
import Axiom.Algebra.FloorAdd.eq.Add_Floor
import Axiom.Algebra.Eq_Add.of.EqSub
import Axiom.Algebra.Eq.of.EqNegS
import Axiom.Algebra.NegSub.eq.Sub
import Axiom.Algebra.Sub_Neg.eq.Add
import Axiom.Algebra.Mod.eq.Sub_Mul_Div
import Axiom.Algebra.EqAddS.of.Eq.Eq
open Algebra


@[main]
private lemma main
  {n d : ℤ} :
-- imply
  ⌈n / (d : ℚ)⌉ = ⌊(d + n - sign d) / (d : ℚ)⌋ := by
-- proof
  by_cases h : (d : ℚ) = 0
  rw [h]
  norm_num
  rw [Ceil.eq.Neg.Floor]
  rw [DivSub.eq.SubDivS]
  rw [DivAdd.eq.AddDivS]
  rw [Div.eq.One.of.Ne_0 h]
  rw [SubAdd.eq.Add_Sub]
  norm_cast
  rw [FloorAdd.eq.Add_Floor.one]
  apply Eq_Add.of.EqSub
  apply Eq.of.EqNegS
  rw [NegSub.eq.Sub]
  rw [Sub_Neg.eq.Add]
  have h₀ := Mod.eq.Sub_Mul_Div (n := -n) (d := d)
  have h₁ := Mod.eq.Sub_Mul_Div (n := (d + n - sign (d))) (d := d)
  ring_nf at h₁
  have := EqAddS.of.Eq.Eq h₀ h₁
  ring_nf at this


-- created on 2025-03-05
-- updated on 2025-03-21
