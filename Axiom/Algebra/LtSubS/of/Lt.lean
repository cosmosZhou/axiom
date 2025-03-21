import Axiom.Algebra.LtAddS.of.Lt
import Axiom.Algebra.Sub.eq.Add_Neg
open Algebra


@[main]
private lemma main
  [OrderedAddCommGroup α]
  {x y : α}
-- given
  (h : x < y)
  (z : α) :
-- imply
  x - z < y - z := by
-- proof
  rw [Sub.eq.Add_Neg (a := x), Sub.eq.Add_Neg (a := y)]
  apply LtAddS.of.Lt h (-z)


-- created on 2024-07-01
