import Axiom.Algebra.LeSubS.of.Le
open Algebra


@[main]
private lemma nat
  {a b c : ℕ}
-- given
  (h : a + b ≤ c) :
-- imply
  a ≤ c - b := by
-- proof
  have h := LeSubS.of.Le.nat h b
  simp at h
  exact h


@[main]
private lemma main
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : a + b ≤ c) :
-- imply
  a ≤ c - b := by
-- proof
  have h := LeSubS.of.Le h b
  simp at h
  exact h


-- created on 2024-11-27
