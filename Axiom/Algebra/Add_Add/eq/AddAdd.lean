import Axiom.Algebra.AddAdd.eq.Add_Add
open Algebra


@[main]
private lemma main
  [AddSemigroup α]
  {a b : α} :
-- imply
  a + (b + c) = a + b + c := by
-- proof
  rw [AddAdd.eq.Add_Add]


-- created on 2024-07-01
