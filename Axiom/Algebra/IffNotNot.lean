import Axiom.Basic
open Algebra


-- 双否定律: double-negation elimination
@[simp, main]
private lemma main
  {p : Prop} :
-- imply
  ¬¬p ↔ p := by
-- proof
  simp


-- created on 2024-07-01
