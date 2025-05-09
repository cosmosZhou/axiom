import stdlib.List.Vector
import Axiom.Algebra.EqMin.of.Le
import Axiom.Algebra.LeSubMulS
import Axiom.Algebra.Mul.comm
open Algebra


@[main]
private lemma main
  {s : List.Vector α (m * n)}
-- given
  (i : Fin m) :
-- imply
  (s.substr (i * n) n).length = n := by
-- proof
  have : (s.substr (i * n) n).length = n ⊓ (m * n - i * n) := by rfl
  rw [this]
  apply EqMin.of.Le
  rw [Mul.comm]
  rw [Mul.comm (b := n)]
  apply LeSubMulS.left


-- created on 2025-05-07
