import Axiom.Algebra.GeAddS.of.Ge
open Algebra


@[main]
private lemma main
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : a - b ≥ c) :
-- imply
  a ≥ c + b := by
-- proof
  have h := GeAddS.of.Ge h b
  simp at h
  exact h


-- created on 2024-11-27
