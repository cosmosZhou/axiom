import Axiom.Algebra.Pow2.ge.One
import Axiom.Algebra.ModEq_Add
import Axiom.Algebra.EqAddSub.of.Le
open Algebra


@[main]
private lemma main
  {n : ℕ} :
-- imply
  2 ^ n ≡ 1 [MOD 2 ^ n - 1] := by
-- proof
  have h_Ge_1 := Pow2.ge.One (n := n)
  let k := 2 ^ n
  have h_eq_k : k = 2 ^ n := rfl
  rw [← h_eq_k]
  rw [← h_eq_k] at h_Ge_1
  have := ModEq_Add (n := k - 1) (k := 1)
  rw [EqAddSub.of.Le h_Ge_1] at this
  assumption


-- created on 2025-03-15
