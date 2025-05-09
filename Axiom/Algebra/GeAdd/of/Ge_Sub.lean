import Axiom.Algebra.GeAddS.of.Ge
open Algebra


@[main]
private lemma nat
  {a b c : ℕ}
-- given
  (h : a ≥ c - b) :
-- imply
  a + b ≥ c := by
-- proof
  have h := GeAddS.of.Ge h b
  simp at h
  exact h


@[main]
private lemma main
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : a ≥ c - b) :
-- imply
  a + b ≥ c := by
-- proof
  have h := GeAddS.of.Ge h b
  simp at h
  exact h


-- created on 2025-05-04
