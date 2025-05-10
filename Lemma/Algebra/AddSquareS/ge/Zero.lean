import Lemma.Algebra.Square.ge.Zero
import Lemma.Algebra.Add.ge.Zero.of.Ge_0.Ge_0
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {a b : α} :
-- imply
  a² + b² ≥ 0 := by
-- proof
  have hₐ := Square.ge.Zero (a := a)
  have h_b := Square.ge.Zero (a := b)
  have := Add.ge.Zero.of.Ge_0.Ge_0 hₐ h_b
  assumption


-- created on 2025-01-16
