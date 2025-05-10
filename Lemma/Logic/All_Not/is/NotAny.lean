import Lemma.Logic.All.is.NotAny_Not
open Logic


@[main]
private lemma main
  {p : α → Prop} :
-- imply
  (∀ x : α, ¬p x) ↔ ¬∃ x : α, p x := by
-- proof
  rw [All.is.NotAny_Not]
  simp


-- created on 2024-07-01
