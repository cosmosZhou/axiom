import Axiom.Algebra.AndOrS.of.OrAnd
import Axiom.Algebra.OrAnd.of.AndOrS
open Algebra


@[main]
private lemma main:
-- imply
  p ∧ q ∨ r ↔ (p ∨ r) ∧ (q ∨ r) :=
-- proof
  ⟨AndOrS.of.OrAnd, OrAnd.of.AndOrS⟩


-- created on 2024-07-01
