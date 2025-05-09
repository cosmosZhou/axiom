import Axiom.Logic.Or.is.NotAndNotS
open Logic


@[main]
private lemma main
  [Decidable a]
  [Decidable b]
  (h : ¬(¬a ∧ ¬b)) :
-- imply
  a ∨ b :=
-- proof
  Or.is.NotAndNotS.mpr h


-- created on 2025-03-29
