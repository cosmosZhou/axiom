import Lemma.Algebra.EqAddS.of.Eq
import Lemma.Algebra.Add.comm
open Algebra


@[main]
private lemma left
  [AddCommGroup α]
  {x a b : α}
-- given
  (h : x - a = b) :
-- imply
  x = a + b := by
-- proof
  have h := EqAddS.of.Eq h a
  simp at h
  rw [Add.comm] at h
  exact h


@[main]
private lemma main
  [AddGroup α]
  {x a b : α}
-- given
  (h : x - b = a) :
-- imply
  x = a + b := by
-- proof
  have h := EqAddS.of.Eq h b
  simp at h
  exact h


-- created on 2024-07-01
-- updated on 2025-04-26
