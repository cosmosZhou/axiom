import Axiom.Set.AndMemS.is.Mem_Inter
open Set


@[main]
private lemma finset
  [DecidableEq ι]
  {A B : Finset ι}
  {e : ι}
-- given
  (h : e ∈ A ∩ B) :
-- imply
  e ∈ A ∧ e ∈ B :=
-- proof
  AndMemS.is.Mem_Inter.finset.mpr h


@[main]
private lemma main
  {A B : Set α}
  {e : α}
-- given
  (h : e ∈ A ∩ B) :
-- imply
  e ∈ A ∧ e ∈ B := 
-- proof
  AndMemS.is.Mem_Inter.mpr h


-- created on 2025-05-01
