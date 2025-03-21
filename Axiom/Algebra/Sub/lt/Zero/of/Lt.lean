import Axiom.Algebra.LtSubS.of.Lt
import Axiom.Algebra.Sub.eq.Zero
open Algebra


@[main]
private lemma main
  [OrderedAddCommGroup α]
  {x y : α}
-- given
  (h : x < y) :
-- imply
  x - y < 0 := by
-- proof
  have := LtSubS.of.Lt h y
  rw [Sub.eq.Zero] at this
  assumption


-- created on 2025-03-15
