import Lemma.Algebra.AddAdd.eq.Add_Add
open Algebra


/--
This lemma provides the reverse direction of the associativity property for addition in a semigroup, demonstrating that `a + (b + c)` can be rewritten as `a + b + c`.
It complements the `AddAdd.eq.Add_Add` axiom, enabling terms to be regrouped in left-associated form during algebraic proofs.
-/
@[main]
private lemma main
  [AddSemigroup α]
  {a b : α} :
-- imply
  a + (b + c) = a + b + c := by
-- proof
  rw [AddAdd.eq.Add_Add]


-- created on 2024-07-01
-- updated on 2025-04-04
