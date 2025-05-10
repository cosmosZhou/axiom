import Lemma.Set.AndNotSMem.of.NotMem_Union
import Lemma.Logic.AndNotS.is.NotOr
open Set Logic


@[main]
private lemma finset
  [DecidableEq ι]
  {A B : Finset ι}
  {e : ι}
-- given
  (h : e ∈ A ∨ e ∈ B) :
-- imply
  e ∈ A ∪ B := by
-- proof
  by_contra h
  have := AndNotSMem.of.NotMem_Union.finset h
  rw [AndNotS.is.NotOr] at this
  contradiction


@[main]
private lemma main
  {A B : Set α}
  {e : α}
-- given
  (h : e ∈ A ∨ e ∈ B) :
-- imply
  e ∈ A ∪ B := by
-- proof
  by_contra h
  have := AndNotSMem.of.NotMem_Union h
  contradiction


-- created on 2025-04-05
-- updated on 2025-04-30
