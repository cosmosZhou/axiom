import Axiom.Algebra.AddMul.lt.Mul
import Axiom.Algebra.Lt_Sub.of.LtAdd
open Algebra


@[main]
private lemma main
-- given
  (i : Fin m)
  (j : Fin n) :
-- imply
  j < m * n - i * n := by
-- proof
  have h := AddMul.lt.Mul i j
  apply Lt_Sub.of.LtAdd.nat.left h


-- created on 2025-05-09
