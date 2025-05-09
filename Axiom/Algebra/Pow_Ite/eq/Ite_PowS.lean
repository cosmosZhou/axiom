import Axiom.Logic.BFn_Ite.eq.Ite_BFnS
open Logic


@[main]
private lemma main
  [Decidable p]
  [HPow α β γ]
  {c : α}
  {a b : β} :
-- imply
  c ^ (if p then
    a
  else
    b) = if p then
    c ^ a
  else
    c ^ b :=
-- proof
  BFn_Ite.eq.Ite_BFnS (f := (· ^ · : α → β → γ))


-- created on 2025-04-27
-- updated on 2025-04-30
