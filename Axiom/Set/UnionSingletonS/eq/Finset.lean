import Axiom.Set.Mem_Finset
open Set


@[main]
private lemma main
  {a b : α} :
-- imply
  {a} ∪ {b} = ({a, b} : Set α) := by
-- proof
  apply ext
  intro x
  -- Use logical equivalences to break down the membership conditions.
  -- The `simp` tactic simplifies the logical conditions using commutativity and associativity of disjunction.
  constructor
  ·
    intro h
    cases' h with h h
    ·
      -- If x ∈ {a}, then x = a.
      rw [h]
      apply Mem_Finset
    ·
      -- If x ∈ {b}, then x = b.
      rw [h]
      simp [Set.mem_singleton]
  ·
    intro h
    cases' h with h h
    ·
      -- If x = a, then x ∈ {a}.
      rw [h]
      apply Mem_Finset
    ·
      -- If x = b, then x ∈ {b}.
      rw [h]
      simp [Set.mem_singleton]




-- created on 2025-04-04
