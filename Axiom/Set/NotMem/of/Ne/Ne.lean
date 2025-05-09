import Axiom.Set.NotMem.of.Ne
import Axiom.Set.NotMem_Union.of.NotMem.NotMem
import Axiom.Set.UnionSingletonS.eq.Finset
open Set


@[main]
private lemma main
  {x a b : α}
-- given
  (h₀ : x ≠ a)
  (h₁ : x ≠ b) :
-- imply
  x ∉ ({a, b} : Set α) := by
-- proof
  have h₀ := NotMem.of.Ne h₀
  have h₁ := NotMem.of.Ne h₁
  have := NotMem_Union.of.NotMem.NotMem h₀ h₁
  -- Use the fact that {a, b} is equivalent to {a} ∪ {b} to rewrite the goal
  rw [UnionSingletonS.eq.Finset] at this
  assumption


-- created on 2025-04-04
