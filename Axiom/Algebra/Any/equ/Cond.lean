import Axiom.Algebra.Cond.of.Any
import Axiom.Algebra.Any.of.Cond
open Algebra


@[simp, main]
private lemma main
  [Inhabited α]:
-- imply
  (∃ _ : α, r) ↔ r :=
-- proof
  ⟨Cond.of.Any, Any.of.Cond (a := default)⟩


-- created on 2024-07-01
