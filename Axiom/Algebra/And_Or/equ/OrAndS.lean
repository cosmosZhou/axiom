import Axiom.Algebra.And_Or.of.OrAndS
import Axiom.Algebra.OrAndS.of.And_Or
open Algebra


@[main]
private lemma main :
-- imply
  p ∧ (q ∨ r) ↔ p ∧ q ∨ p ∧ r :=
-- proof
  ⟨OrAndS.of.And_Or, And_Or.of.OrAndS⟩


-- created on 2024-07-01
