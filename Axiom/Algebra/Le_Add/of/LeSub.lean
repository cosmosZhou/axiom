import Axiom.Algebra.LeAddS.of.Le
open Algebra


@[main]
private lemma main
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : a - b ≤ c) :
-- imply
  a ≤ c + b := by
-- proof
  have h := LeAddS.of.Le h b
  simp at h
  exact h


-- created on 2024-11-27
-- updated on 2025-04-30
