import Axiom.Basic


@[main]
private lemma main
  {a b : α} :
-- imply
  (a = b) ↔ (b = a) :=
-- proof
  ⟨fun h => h.symm, fun h => h.symm⟩


-- created on 2025-01-12
