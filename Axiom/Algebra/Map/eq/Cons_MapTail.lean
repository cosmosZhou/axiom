import Axiom.Basic


@[main]
private lemma main
  {s : Vector α (Nat.succ n)}
  {f : α → β} :
-- imply
  s.map f = f s.head ::ᵥ s.tail.map f := by
-- proof
  have h : s = s.head ::ᵥ s.tail := by simp
  -- rewrite only the left-hand side
  rw [h]
  apply Mathlib.Vector.map_cons


-- created on 2024-07-01
