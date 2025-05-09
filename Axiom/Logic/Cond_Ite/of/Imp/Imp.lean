import Axiom.Logic.Cond_Ite.of.AndImpS
open Logic


@[main]
private lemma main
  [Decidable p]
  {R : α → β → Prop}
  {x : α}
  {a b : β}
-- given
  (h₀ : p → R x a)
  (h₁ : ¬p → R x b) :
-- imply
  R x (if p then
    a
  else
    b) :=
-- proof
  Cond_Ite.of.AndImpS ⟨h₀, h₁⟩


-- created on 2025-03-21
-- updated on 2025-04-11
