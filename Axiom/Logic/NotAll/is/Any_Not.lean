import Axiom.Logic.Any_Not.is.NotAll
open Logic


@[main]
private lemma finset
  {p : ι → Prop}
  {s : Finset ι} :
-- imply
  (¬∀ x : s, p x) ↔ ∃ x : s, ¬p x :=
-- proof
  Any_Not.is.NotAll.finset.symm


@[main]
private lemma main
  {p : α → Prop} :
-- imply
  (¬∀ x : α, p x) ↔ ∃ x : α, ¬p x :=
-- proof
  Any_Not.is.NotAll.symm


-- created on 2024-07-01
