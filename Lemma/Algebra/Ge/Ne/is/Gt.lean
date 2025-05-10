import Lemma.Algebra.Gt.of.Ge.Ne
import Lemma.Algebra.Ge.Ne.of.Gt
open Algebra


@[main]
private lemma main
  [LinearOrder α]
  {a b : α} :
-- imply
  a ≥ b ∧ a ≠ b ↔ a > b :=
-- proof
  ⟨fun h_And => Gt.of.Ge.Ne h_And.left h_And.right, Ge.Ne.of.Gt⟩


-- created on 2025-04-18
