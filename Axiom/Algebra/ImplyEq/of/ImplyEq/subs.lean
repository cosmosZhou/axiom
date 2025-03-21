import Axiom.Algebra.Imply_And.of.Imply
open Algebra


@[main]
private lemma main
  {a b : α}
  {p : α → Prop}
-- given
  (h : a = b → p a) :
-- imply
  a = b → p b := by
-- proof
  intro h_eq
  have h_And := (Imply_And.of.Imply h) h_eq
  exact h_And.left ▸ h_And.right


-- created on 2025-01-12
