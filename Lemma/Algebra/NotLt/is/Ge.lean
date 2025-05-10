import Lemma.Algebra.Ge.of.NotLt
import Lemma.Algebra.NotLt.of.Ge
open Algebra


@[main]
private lemma main
  [LinearOrder α]
  {a b : α} :
-- imply
  ¬a < b ↔ a ≥ b :=
-- proof
  ⟨Ge.of.NotLt, NotLt.of.Ge⟩


-- created on 2025-04-18
