import Axiom.Algebra.And.of.And.symm
open Algebra


@[main]
private lemma main :
-- imply
  p ∧ q ↔ q ∧ p :=
-- proof
  ⟨
    And.of.And.symm,
    And.of.And.symm
  ⟩


-- created on 2024-07-01
