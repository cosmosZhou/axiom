import stdlib.List.Vector
import Axiom.Algebra.SumCons.eq.Add_Sum
open Algebra


@[main]
private lemma main
  [Add α] [Zero α]
  {l : List.Vector α n}
  {a : α} :
-- imply
  (a ::ᵥ l).sum = a + l.sum :=
-- proof
  SumCons.eq.Add_Sum


-- created on 2024-07-01
