import stdlib.List.Vector
import Axiom.Basic


@[main]
private lemma main
  [Add α] [Zero α] [Mul α]
  {a a' : α}
  {s s' : List.Vector α n} :
-- imply
  (a ::ᵥ s) ⬝ (a' ::ᵥ s') = a * a' + s ⬝ s' := by
-- proof
  rfl


-- created on 2024-07-01
