import Lemma.Algebra.Sub.eq.Add_Neg
import Lemma.Algebra.LeAddS.of.Le
open Algebra


@[main]
private lemma nat
  {x y : ℕ}
-- given
  (h : x ≤ y)
  (z : ℕ) :
-- imply
  x - z ≤ y - z := by
-- proof
  apply Nat.sub_le_sub_right h


@[main]
private lemma main
  [OrderedAddCommGroup α]
  {x y : α}
-- given
  (h : x ≤ y)
  (z : α) :
-- imply
  x - z ≤ y - z := by
-- proof
  rw [Sub.eq.Add_Neg (a := x), Sub.eq.Add_Neg (a := y)]
  apply LeAddS.of.Le h (-z)


-- created on 2024-07-01
