import Axiom.Logic.Cond_Ite.of.OrAndS
open Logic


@[main]
private lemma main
  [Decidable p]
  {S : Set α}
  {a b : α}
-- given
  (h : (a ∈ S ∧ p) ∨ (b ∈ S ∧ ¬p)) :
-- imply
  (if p then
    a
  else
    b) ∈ S :=
-- proof
  Cond_Ite.of.OrAndS h


-- created on 2025-04-20
