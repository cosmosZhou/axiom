import Axiom.Algebra.Or.of.Or.symm
open Algebra


@[main]
private lemma main :
-- imply
  p ∨ q ↔ q ∨ p :=
-- proof
  ⟨
    Or.of.Or.symm,
    Or.of.Or.symm
  ⟩


-- created on 2024-07-01
