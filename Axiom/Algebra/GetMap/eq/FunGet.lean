import Axiom.Basic


@[simp, main]
private lemma main
  (v : Vector α n)
  (f : α → β)
  (i : Fin n) :
-- imply
  (v.map f).get i = f (v.get i) := by
-- proof
  simp [Mathlib.Vector.get_map]


-- created on 2024-07-01
