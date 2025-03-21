import Axiom.Basic


@[simp, main]
private lemma main
  {l : List α} :
-- imply
  (a :: l.tail).tail = l.tail := by
-- proof
  rfl


-- created on 2024-07-01
