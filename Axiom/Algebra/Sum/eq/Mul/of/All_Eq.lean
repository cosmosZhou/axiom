import sympy.sets.sets
import Axiom.Algebra.Sum.eq.SMulCard.of.All_Eq
open Algebra


@[main]
private lemma main
  [Ring α]
  {x : ℕ → α}
  {a : α}
  {n : ℕ}
-- given
  (h : ∀ i ∈ range n, x i = a) :
-- imply
  ∑ i ∈ range n, x i = n * a := by
-- proof
  have := Sum.eq.SMulCard.of.All_Eq h
  simp at this
  assumption


-- created on 2025-04-26
