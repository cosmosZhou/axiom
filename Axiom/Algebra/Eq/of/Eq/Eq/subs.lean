import Axiom.Algebra.Imply_And.of.Imply
open Algebra


@[main]
private lemma main
  {a b : α}
  {p q : α → β}
-- given
  (h0 : a = b)
  (h1 : p a = q a) :
-- imply
  p b = q b := by
-- proof
  exact h0 ▸ h1


-- created on 2025-01-12
