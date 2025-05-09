import Axiom.Logic.Any.is.NotAll_Not
open Logic


@[main]
private lemma finset
  {p : ι → Prop}
  {s : Finset ι} :
-- imply
  (∃ x : s, ¬p x) ↔ ¬∀ x : s, p x := by
-- proof
    -- Apply the push_neg tactic to transform the goal using De Morgan's laws
  push_neg
    -- The goal now matches the left-hand side of the equivalence, proving the lemma
  rfl


@[main]
private lemma main
  {p : α → Prop} :
-- imply
  (∃ x : α, ¬p x) ↔ ¬∀ x : α, p x := by
-- proof
  rw [Any.is.NotAll_Not]
  simp


-- created on 2024-07-01
-- updated on 2025-04-06
