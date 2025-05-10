import Lemma.Set.Mem.of.Mem.Subset
open Set


@[main]
private lemma main
  {A B : Set α}
-- given
  (h : A ⊆ B) :
-- imply
  A ∪ B = B := by
-- proof
  -- We will show that each set is a subset of the other.
  apply Set.ext
  intro x
  -- For any element x, we need to show that x ∈ A ∪ B ↔ x ∈ B.
  constructor
  ·
    intro h'
    simp [h] at h'
    cases' h' with h_A h_B
    ·
      -- exact h h_A
      apply Mem.of.Mem.Subset h_A h
    ·
      assumption
  ·
    tauto


-- created on 2025-04-05
