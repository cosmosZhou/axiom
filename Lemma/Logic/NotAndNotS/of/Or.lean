import Lemma.Logic.Or.is.NotAndNotS
open Logic


@[main]
private lemma main
  [Decidable a]
  [Decidable b]
-- given
  (h : a ∨ b) :
-- imply
  ¬(¬a ∧ ¬b) :=
-- proof
  Or.is.NotAndNotS.mp h


-- created on 2025-03-29
