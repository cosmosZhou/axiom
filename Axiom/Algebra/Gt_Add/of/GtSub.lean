import Axiom.Algebra.GtAddS.of.Gt
open Algebra


@[main]
private lemma main
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : a - b > c) :
-- imply
  a > c + b := by
-- proof
  have h := GtAddS.of.Gt h b
  simp at h
  exact h


-- created on 2024-11-26
