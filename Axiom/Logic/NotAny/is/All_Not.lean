import Axiom.Logic.All_Not.is.NotAny
open Logic


@[main]
private lemma main
  {p : α → Prop} :
-- imply
  (¬∃ x : α, p x) ↔ ∀ x : α, ¬p x :=
-- proof
  All_Not.is.NotAny.symm


-- created on 2024-07-01
