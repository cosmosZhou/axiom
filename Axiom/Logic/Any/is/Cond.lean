import Axiom.Logic.Cond.of.Any
import Axiom.Logic.Any.of.Cond
open Logic


@[main]
private lemma main
  [Inhabited α]:
-- imply
  (∃ _ : α, r) ↔ r :=
-- proof
  ⟨Cond.of.Any, Any.of.Cond (a := default)⟩


-- created on 2024-07-01
