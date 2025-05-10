import stdlib.Slice
import Lemma.Algebra.Tail.eq.Drop_1
open Algebra


@[main]
private lemma main
  {s : List α} :
-- imply
  s.drop 1 = s.tail :=
-- proof
  Tail.eq.Drop_1.symm


-- created on 2025-05-05
