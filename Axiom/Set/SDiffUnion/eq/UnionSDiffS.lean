import Axiom.Set.Mem_Union.of.Mem
open Set


@[main]
private lemma main
  {A B C : Set α} :
-- imply
  (A ∪ B) \ C = (A \ C) ∪ (B \ C) := by
-- proof
  ext x
  constructor <;> intro h
  ·
    let ⟨hAB, hC⟩ := h
    cases' hAB with hA hB
    ·
      apply Mem_Union.of.Mem (B := B \ C)
      simp [hA, hC]
    ·
      apply Mem_Union.of.Mem (B := A \ C) (left := true)
      simp [hB, hC]
  ·
    cases' h with hAC hBC
    ·
      let ⟨hA, hC⟩ := hAC
      constructor
      ·
        apply Mem_Union.of.Mem hA B
      ·
        assumption
    ·
      let ⟨hB, hC⟩ := hBC
      constructor
      ·
        apply Mem_Union.of.Mem hB A (left := true)
      ·
        assumption


-- created on 2025-04-06
