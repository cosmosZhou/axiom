import Axiom.Algebra.ImplyEq.of.ImplyEq.subs
import Axiom.Algebra.Eq.comm
open Algebra


@[main]
private lemma main
  {a b : α}
  {p : α → Prop} :
-- imply
  (a = b → p a) ↔ (a = b → p b) := by
-- proof
  constructor
  apply ImplyEq.of.ImplyEq.subs
  rw [Eq.comm (a := a) (b := b)]
  apply ImplyEq.of.ImplyEq.subs


-- created on 2025-01-12
