import stdlib.Slice
import Axiom.Algebra.DropDrop.eq.Drop_Add
open Algebra


@[main]
private lemma main
  {s : List α} :
-- imply
  s.drop (i + j) = (s.drop i).drop j := 
-- proof
  DropDrop.eq.Drop_Add.symm


-- created on 2025-05-08
