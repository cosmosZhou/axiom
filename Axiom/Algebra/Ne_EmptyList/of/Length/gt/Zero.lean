import stdlib.List.Vector
import Axiom.Algebra.Ne.of.Gt
import Axiom.Algebra.Ne_EmptyList.of.Length.ne.Zero
open Algebra


@[main]
private lemma main
  {v : List α}
-- given
  (h : v.length > 0) :
-- imply
  v ≠ [] := by
-- proof
  have h := Ne.of.Gt h
  apply Ne_EmptyList.of.Length.ne.Zero h


-- created on 2025-05-08
