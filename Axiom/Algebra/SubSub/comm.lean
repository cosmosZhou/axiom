import Axiom.Basic


@[main]
private lemma nat
  {a b c : ℕ} :
-- imply
  a - b - c = a - c - b := by
-- proof
   -- Use the `Nat.sub_sub` lemma to rewrite subtraction in terms of addition, then apply commutativity of addition.
  simp [Nat.sub_sub, add_comm, add_left_comm, add_assoc]


/--
This lemma demonstrates that in an additive commutative group, the order of subtraction of two elements does not affect the result.
Specifically, it shows that subtracting `b` and then `c` from `a` yields the same value as subtracting `c` and then `b`, leveraging the commutativity of the group operation.
-/
@[main]
private lemma main
  [AddCommGroup α]
  {a b c : α} :
-- imply
  a - b - c = a - c - b := by
-- proof
  abel


-- created on 2025-03-24
-- updated on 2025-05-04
