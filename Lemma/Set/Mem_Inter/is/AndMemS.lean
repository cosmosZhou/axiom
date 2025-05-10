import Lemma.Basic


@[main]
private lemma finset
  [DecidableEq ι]
  {A B : Finset ι}
  {e : ι} :
-- imply
  e ∈ A ∩ B ↔ e ∈ A ∧ e ∈ B :=
-- proof
  Finset.mem_inter


@[main]
private lemma main
  {A B : Set α}
  {e : α} :
-- imply
  e ∈ A ∩ B ↔ e ∈ A ∧ e ∈ B :=
-- proof
  Set.mem_inter_iff e A B


-- created on 2025-05-01
