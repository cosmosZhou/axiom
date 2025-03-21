import Axiom.Algebra.And_Not.of.NotImply
import Axiom.Algebra.NotImply.of.And_Not
open Algebra


@[main]
private lemma main :
-- imply
  ¬(p → q) ↔ p ∧ ¬q :=
-- proof
  ⟨And_Not.of.NotImply, NotImply.of.And_Not⟩


-- created on 2024-07-01
