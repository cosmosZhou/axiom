import Axiom.Set.NotMem.of.NotMem.Subset
open Set


@[main]
private lemma main
  {B C : Set α}
-- given
  (h : C ⊆ B)
  (A : Set α) :
-- imply
  (A \ B) \ C = A \ B := by
-- proof
  -- Use the extensionality axiom to show that two sets are equal by showing they have the same elements.
  ext x
  constructor <;>
    intro ⟨_, h_NotIn⟩
  ·
    simp_all [Set.mem_diff, h]
  ·
    simp_all [Set.mem_diff, h]
    apply NotMem.of.NotMem.Subset h_NotIn h


-- created on 2025-04-08
