import Axiom.Basic


@[main]
private lemma main
  [Add α] [Zero α] [Mul α]
  {a a' : α}
  {s s' : Vector α n} :
-- imply
  (a ::ᵥ s) ⬝ (a' ::ᵥ s') = a * a' + s ⬝ s' := by
-- proof
  simp [Mathlib.Vector.dot]


-- created on 2024-07-01
