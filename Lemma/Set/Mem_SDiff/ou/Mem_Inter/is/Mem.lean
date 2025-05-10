import Lemma.Set.Mem.is.Mem_Inter.ou.Mem_SDiff
open Set


@[main]
private lemma finset
  [DecidableEq ι]
  {A B : Finset ι}
  {x : ι} :
-- imply
  x ∈ A \ B ∨ x ∈ A ∩ B ↔ x ∈ A := by
-- proof
  rw [Iff.comm]
  rw [Or.comm]
  apply Mem.is.Mem_Inter.ou.Mem_SDiff.finset


@[main]
private lemma main
  {A B : Set α}
  {x : α} :
-- imply
  x ∈ A \ B ∨ x ∈ A ∩ B ↔ x ∈ A := by
-- proof
  rw [Iff.comm]
  rw [Or.comm]
  apply Mem.is.Mem_Inter.ou.Mem_SDiff


-- created on 2025-04-30
-- updated on 2025-05-01
