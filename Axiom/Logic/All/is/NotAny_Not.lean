import Axiom.Logic.Any.is.NotAll_Not
open Logic


@[main]
private lemma main
  {p : α → Prop} :
-- imply
  (∀ x : α, p x) ↔ ¬∃ x : α, ¬p x := by
-- proof
  rw [Any.is.NotAll_Not]
  simp


-- created on 2024-07-01
