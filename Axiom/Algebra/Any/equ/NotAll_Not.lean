import Axiom.Algebra.NotAll_Not.of.Any
import Axiom.Algebra.Any.of.NotAll_Not
open Algebra


@[main]
private lemma main
  {p : α → Prop} :
-- imply
  (∃ x : α, p x) ↔ ¬∀ x : α, ¬p x :=
-- proof
  ⟨NotAll_Not.of.Any, Any.of.NotAll_Not⟩


-- created on 2024-07-01
