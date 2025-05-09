import Axiom.Algebra.LeAdd_1.of.Lt
open Algebra


@[main]
private lemma main
  {n : ℕ} 
  {i : Fin n}:
-- imply
  i + 1 ≤ n := by
-- proof
  
  apply LeAdd_1.of.Lt
  simp


-- created on 2025-05-06
