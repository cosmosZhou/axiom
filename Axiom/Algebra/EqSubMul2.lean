import Axiom.Algebra.Mul2.eq.Add
import Axiom.Algebra.EqSubAdd
open Algebra


@[main]
private lemma nat
  {x : ℕ} :
-- imply
  2 * x - x = x := by
-- proof
  rw [Mul2.eq.Add]
  simp


@[main]
private lemma main
  [Ring α]
  {x : α} :
-- imply
  2 * x - x = x := by
-- proof
  rw [Mul2.eq.Add]
  rw [EqSubAdd]


-- created on 2025-05-04
