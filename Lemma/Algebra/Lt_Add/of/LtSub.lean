import Lemma.Algebra.LtAddS.of.Lt
open Algebra


@[main]
private lemma main
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : a - b < c) :
-- imply
  a < c + b := by
-- proof
  have h := LtAddS.of.Lt h b
  simp at h
  exact h


-- created on 2024-11-27
