import sympy.sets.sets
import Lemma.Set.Mem_IocDivS.of.Mem_Ioc.Gt_0
import Lemma.Algebra.Div0.eq.Zero
import Lemma.Algebra.Div.eq.One.of.Gt_0
import Lemma.Set.Ceil.eq.One.of.Mem_Ioc01
open Set Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  [FloorRing α]
  {a b : α}
-- given
  (h₀ : b > 0)
  (h₁ : a ∈ Ioc 0 b) :
-- imply
  ⌈a / b⌉ = 1 := by
-- proof
  have := Mem_IocDivS.of.Mem_Ioc.Gt_0 h₀ h₁
  simp only [Div0.eq.Zero] at this
  simp only [Div.eq.One.of.Gt_0 h₀] at this
  apply Ceil.eq.One.of.Mem_Ioc01 this


-- created on 2025-05-04
