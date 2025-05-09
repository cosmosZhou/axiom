import Axiom.Logic.OrAnyS.of.Any_Or
import Axiom.Logic.Any_Or.of.OrAnyS
open Logic


@[main]
private lemma main
  {p q : α → Prop} :
-- imply
  (∃ x : α, p x ∨ q x) ↔  (∃ x : α, p x) ∨ (∃ x : α, q x) :=
-- proof
  ⟨OrAnyS.of.Any_Or, Any_Or.of.OrAnyS⟩


-- created on 2024-07-01
