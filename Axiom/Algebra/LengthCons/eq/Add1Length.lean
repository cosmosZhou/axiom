import Axiom.Algebra.Add.comm
open Algebra


@[main]
private lemma main
-- given
  (a : α)
  (l : List α) :
-- imply
  (a :: l).length = 1 + l.length := by
-- proof
  have := List.length_cons a l
  rw [Add.comm] at this
  assumption


-- created on 2025-05-08
