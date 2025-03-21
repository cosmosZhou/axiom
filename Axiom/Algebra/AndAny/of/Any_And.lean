import Axiom.Algebra.Any.of.Any_And
import Axiom.Algebra.Cond.of.Any
open Algebra


@[main]
private lemma main
  {r :Prop}
  {p : α → Prop}
-- given
  (h : ∃ x : α, p x ∧ r) :
-- imply
  (∃ x : α, p x) ∧ r :=
-- proof
  ⟨
    Any.of.Any_And h,
    Cond.of.Any (
      Any.of.Any_And h false
    )
  ⟩


-- created on 2024-07-01
