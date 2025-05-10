import Lemma.Set.Mem_Inter.is.AndMemS
open Set


@[main]
private lemma finset
  [DecidableEq ι]
  {A B : Finset ι}
  {e : ι}
-- given
  (h : e ∈ A ∧ e ∈ B) :
-- imply
  e ∈ A ∩ B :=
-- proof
  Mem_Inter.is.AndMemS.finset.mpr h


@[main]
private lemma main
  {A B : Set α}
  {e : α}
-- given
  (h : e ∈ A ∧ e ∈ B) :
-- imply
  e ∈ A ∩ B :=
-- proof
  Mem_Inter.is.AndMemS.mpr h


-- created on 2025-05-01
