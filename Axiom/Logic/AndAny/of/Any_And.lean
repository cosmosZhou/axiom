import Axiom.Logic.Any.of.Any_And
import Axiom.Logic.Cond.of.Any
open Logic


@[main]
private lemma main
  {r : Prop}
  {p : α → Prop}
-- given
  (h : ∃ x : α, p x ∧ r) :
-- imply
  (∃ x : α, p x) ∧ r :=
-- proof
  ⟨
    Any.of.Any_And.left h,
    Cond.of.Any (
      Any.of.Any_And h)
  ⟩


-- created on 2024-07-01
-- updated on 2025-04-29
