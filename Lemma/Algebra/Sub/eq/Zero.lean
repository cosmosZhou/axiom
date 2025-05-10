import Lemma.Basic


/--
In any additive group `α`, subtracting an element `a` from itself yields the additive identity `0`.
This fundamental property, expressed as `a - a = 0`, is essential for simplifying expressions and streamlining proofs involving group operations.
-/
@[main]
private lemma main
  [AddGroup α]
  {a : α} :
-- imply
  a - a = 0 := by
-- proof
  rw [sub_self]


-- created on 2024-07-01
-- updated on 2025-04-04
