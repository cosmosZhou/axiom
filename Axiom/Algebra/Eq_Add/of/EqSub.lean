import Axiom.Algebra.EqAddS.of.Eq
open Algebra


@[main]
private lemma main
  [AddGroup α]
  {x a b: α}
-- given
  (h : x - b = a) :
-- imply
  x = a + b := by
-- proof
  have h := EqAddS.of.Eq h b
  simp at h
  exact h


-- created on 2024-07-01
