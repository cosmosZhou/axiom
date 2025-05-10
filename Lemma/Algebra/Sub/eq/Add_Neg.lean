import Lemma.Basic


/--
This lemma demonstrates that in a `SubNegMonoid`, subtraction of two elements `a` and `b` is equivalent to adding the additive inverse of `b` to `a`.
Specifically, it states that `a - b = a + -b`, leveraging the algebraic property that subtraction can be defined as addition of the inverse.
This identity is fundamental for simplifying expressions and proving further algebraic properties within structures that support subtraction and negation.
-/
@[main]
private lemma main
  [SubNegMonoid α]
  {a b : α} :
-- imply
  a - b = a + -b := by
-- proof
  rw [sub_eq_add_neg]


-- created on 2024-07-01
-- updated on 2025-04-04
