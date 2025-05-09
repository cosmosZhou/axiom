import Axiom.Algebra.Inv.lt.Zero.of.Lt_0
import Axiom.Algebra.Lt_0.of.Inv.lt.Zero
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {x : α} :
-- imply
  x⁻¹ < 0 ↔ x < 0 :=
-- proof
  ⟨Lt_0.of.Inv.lt.Zero, Inv.lt.Zero.of.Lt_0⟩


-- created on 2025-03-30
