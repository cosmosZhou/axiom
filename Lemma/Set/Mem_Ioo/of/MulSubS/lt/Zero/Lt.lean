import Lemma.Algebra.OrAndSLt_0Gt_0.of.Mul.lt.Zero
import Lemma.Algebra.Lt.of.Sub.lt.Zero
import Lemma.Algebra.Gt.of.Sub.gt.Zero
import Lemma.Algebra.Gt.of.Gt.Gt
import Lemma.Algebra.NotLt.of.Gt
import Lemma.Set.Mem_Ioo.of.Gt.Lt
open Algebra Set


@[main]
private lemma main
  [LinearOrderedRing α]
  {a b : α}
-- given
  (h₀ : (x - a) * (x - b) < 0)
  (h₁ : a < b) :
-- imply
  x ∈ Ioo a b := by
-- proof
  have h_Or := OrAndSLt_0Gt_0.of.Mul.lt.Zero h₀
  rcases h_Or with h_And | h_And
  ·
    let ⟨h_Lt, h_Gt⟩ := h_And
    have h_Lt := Lt.of.Sub.lt.Zero h_Lt
    have h_Gt := Gt.of.Sub.gt.Zero h_Gt
    have := Gt.of.Gt.Gt h_Lt h_Gt
    have := NotLt.of.Gt this
    contradiction
  ·
    let ⟨h_Lt, h_Gt⟩ := h_And
    have h_Lt := Lt.of.Sub.lt.Zero h_Lt
    have h_Gt := Gt.of.Sub.gt.Zero h_Gt
    apply Mem_Ioo.of.Gt.Lt h_Gt h_Lt


-- created on 2025-03-30
