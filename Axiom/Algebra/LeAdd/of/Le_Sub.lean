import Axiom.Algebra.LeAddS.of.Le
open Algebra


@[main]
private lemma main
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : a ≤ c - b) :
-- imply
  a + b ≤ c := by
-- proof
  have h := LeAddS.of.Le h b
  simp at h
  exact h


-- created on 2025-03-30
-- updated on 2025-04-30
