import Axiom.Set.OrMemS.of.Mem_Union
import Axiom.Set.Mem_Union.of.OrMemS
open Set


@[main]
private lemma finset
  [DecidableEq ι]
  {A B : Finset ι}
  {e : ι} :
-- imply
  e ∈ A ∪ B ↔ e ∈ A ∨ e ∈ B :=
-- proof
  ⟨OrMemS.of.Mem_Union.finset, Mem_Union.of.OrMemS.finset⟩


@[main]
private lemma main
  {A B : Set α}
  {e : α} :
-- imply
  e ∈ A ∪ B ↔ e ∈ A ∨ e ∈ B :=
-- proof
  ⟨OrMemS.of.Mem_Union, Mem_Union.of.OrMemS⟩


-- created on 2025-04-30
-- updated on 2025-05-01
