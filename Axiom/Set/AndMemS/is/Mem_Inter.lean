import Axiom.Set.Mem_Inter.is.AndMemS
open Set


@[main]
private lemma finset
  [DecidableEq ι]
  {A B : Finset ι}
  {e : ι} :
-- imply
  e ∈ A ∧ e ∈ B ↔ e ∈ A ∩ B :=
-- proof
  Mem_Inter.is.AndMemS.finset.symm


@[main]
private lemma main
  {A B : Set α}
  {e : α} :
-- imply
  e ∈ A ∧ e ∈ B ↔ e ∈ A ∩ B :=
-- proof
  Mem_Inter.is.AndMemS.symm


-- created on 2025-05-01
