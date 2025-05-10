import Lemma.Algebra.LengthFlatten.eq.SumMapLength
open Algebra


@[main]
private lemma main
-- given
  (L : List (List α)) :
-- imply
  (L.map List.length).sum = L.flatten.length :=
-- proof
  (LengthFlatten.eq.SumMapLength L).symm


-- created on 2025-05-08
