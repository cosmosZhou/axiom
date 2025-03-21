import Axiom.Basic


@[main]
private lemma main
-- given
  (h : p ∨ q) :
-- imply
  q ∨ p :=
-- proof
  h.elim (fun p ↦ Or.inr p) (fun q ↦ Or.inl q)


-- created on 2024-07-01
