import Axiom.Logic.All.is.NotAny_Not
open Logic


@[main]
private lemma main
  {p : α → Prop} :
-- imply
  (¬∃ x : α, ¬p x) ↔ ∀ x : α, p x :=
-- proof
  All.is.NotAny_Not.symm


-- created on 2024-07-01
