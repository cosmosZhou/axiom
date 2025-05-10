import Lemma.Algebra.FMod.eq.Sub_MulFDiv
import Lemma.Algebra.EqSub.of.Eq_Add
import Lemma.Algebra.Add.comm
import Lemma.Algebra.Eq_Add.of.EqSub
import Lemma.Algebra.Sub.eq.Zero
import Lemma.Set.FDiv.eq.Zero.of.Lt_0.IccAdd_1'0
open Algebra Set


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h₀ : d < 0)
  (h₁ : n ∈ Icc (d + 1) 0) :
-- imply
  n.fmod d = n := by
-- proof
  rw [FMod.eq.Sub_MulFDiv]
  apply EqSub.of.Eq_Add
  rw [Add.comm]
  apply Eq_Add.of.EqSub
  rw [Sub.eq.Zero]
  have := FDiv.eq.Zero.of.Lt_0.IccAdd_1'0 h₀ h₁
  rw [this]
  simp


-- created on 2025-03-29
-- updated on 2025-03-30
