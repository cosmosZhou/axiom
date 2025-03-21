import Axiom.Basic


@[simp, main]
private lemma main
  {l : Vector α n} :
-- imply
  (a ::ᵥ l.tail).tail = l.tail := by
-- proof
  rfl


-- created on 2024-07-01
