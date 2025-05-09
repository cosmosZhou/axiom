import Axiom.Algebra.LtAddS.of.Lt
open Algebra


@[main]
private lemma main
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : a < c - b) :
-- imply
  a + b < c := by
-- proof
  have h := LtAddS.of.Lt h b
  simp at h
  exact h


-- created on 2025-04-06
