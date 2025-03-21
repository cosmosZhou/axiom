import Axiom.Algebra.GeSubS.of.Ge
open Algebra


@[main]
private lemma main
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : a + b ≥ c) :
-- imply
  a ≥ c - b := by
-- proof
  have h := GeSubS.of.Ge h b
  simp at h
  simp
  exact h


-- created on 2024-11-27
