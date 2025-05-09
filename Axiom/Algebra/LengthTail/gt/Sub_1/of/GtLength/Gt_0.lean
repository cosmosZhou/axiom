import stdlib.Slice
import Axiom.Algebra.Le.of.Lt_Add_1
import Axiom.Algebra.Gt.of.Ge.Gt
import Axiom.Algebra.LtSub_1.of.Le.Gt_0
open Algebra


@[main]
private lemma main
  {s : List α}
-- given
  (h₀ : i > 0)
  (h₁ : s.length > i) :
-- imply
  s.tail.length > i - 1 := by
-- proof
  match s with
  | .nil =>
    simp
    contradiction
  | head :: tail =>
    -- For a non-empty list, the tail's length is s.length.
    -- From the induction hypothesis, we know s.length > i - 1.
    simp_all [Nat.succ_eq_add_one]
    -- Use omega to solve the inequality involving natural numbers.
    have h_Le := Le.of.Lt_Add_1 h₁
    have := Gt.of.Ge.Gt h_Le h₀
    apply LtSub_1.of.Le.Gt_0 this h_Le


-- created on 2025-05-05
