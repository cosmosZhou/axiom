import Lemma.Algebra.Le_Sub_1.of.Lt
open Algebra


@[main]
private lemma main
-- given
  (i : Fin n):
-- imply
  i ≤ n - 1 := by
-- proof
  have : i < n := by simp
  apply Le_Sub_1.of.Lt this


-- created on 2025-05-07
