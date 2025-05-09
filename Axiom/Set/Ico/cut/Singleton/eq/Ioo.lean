import Axiom.Algebra.Gt.of.Ge.Ne
import Axiom.Set.Mem_Ioo.of.Gt.Lt
import Axiom.Algebra.Ne.of.Gt
import Axiom.Set.Mem_Ico.of.Lt.Ge
import Axiom.Algebra.Ge.of.Gt
open Set Algebra


@[main]
private lemma main
  [LinearOrder α]
  {a b : α} :
-- imply
  Ico a b \ {a} = Ioo a b := by
-- proof
  ext x
  constructor <;>
    intro h
  ·
    let ⟨h₀, h₁⟩ := h
    simp at h₁
    let ⟨h₀, h₂⟩ := h₀
    have := Gt.of.Ge.Ne h₀ h₁
    apply Mem_Ioo.of.Gt.Lt this h₂
  ·
    let ⟨h₀, h₁⟩ := h
    constructor
    ·
      apply Mem_Ico.of.Lt.Ge h₁
      apply Ge.of.Gt h₀
    ·
      simp
      apply Ne.of.Gt h₀


-- created on 2025-04-04
