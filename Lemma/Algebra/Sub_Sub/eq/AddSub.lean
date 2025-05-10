import Lemma.Algebra.AddSub.eq.SubAdd
open Algebra


/--
This lemma demonstrates that in an additive commutative group, subtracting a subtraction expression `b - c` from `a` is equivalent to first subtracting `b` from `a` and then adding `c`.
The proof leverages the property `sub_sub_eq_add_sub` to rewrite `a - (b - c)` as `a + c - b`, followed by applying `AddSub.eq.SubAdd` to rearrange the terms into the final form `a - b + c`.
-/
@[main]
private lemma main
  -- [SubtractionMonoid α]
  [AddCommGroup α]
  {a b c : α} :
-- imply
  a - (b - c) = a - b + c := by
-- proof
  rw [sub_sub_eq_add_sub]
  rw [AddSub.eq.SubAdd]


-- created on 2025-03-24
-- updated on 2025-04-04
