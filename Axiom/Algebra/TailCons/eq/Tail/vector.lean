import stdlib.List.Vector
import Axiom.Basic


@[main]
private lemma main
-- given
  (l : List.Vector α n)
  (a : α):
-- imply
  (a ::ᵥ l.tail).tail = l.tail := by
-- proof
  rfl


-- created on 2024-07-01
