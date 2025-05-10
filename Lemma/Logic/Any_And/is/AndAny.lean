import Lemma.Logic.AndAny.of.Any_And
import Lemma.Logic.Any_And.of.AndAny
open Logic


@[main]
private lemma main
  {r :Prop}
  {p : α → Prop} :
-- imply
  (∃ x : α, p x ∧ r) ↔ (∃ x : α, p x) ∧ r :=
-- proof
  ⟨AndAny.of.Any_And, Any_And.of.AndAny⟩


-- created on 2024-07-01
