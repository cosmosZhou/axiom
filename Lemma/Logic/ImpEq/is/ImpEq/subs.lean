import Lemma.Logic.ImpEq.of.ImpEq.subs
open Logic


@[main]
private lemma main
  {a b : α}
  {p : α → Prop} :
-- imply
  (a = b → p a) ↔ (a = b → p b) := by
-- proof
  constructor
  apply ImpEq.of.ImpEq.subs
  rw [Eq.comm (a := a) (b := b)]
  apply ImpEq.of.ImpEq.subs


-- created on 2025-01-12
-- updated on 2025-04-19
