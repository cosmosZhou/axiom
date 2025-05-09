import Axiom.Set.EqUnionInter__SDiff
import Axiom.Set.IffMemS.of.Eq
import Axiom.Set.Mem_Union.is.OrMemS
open Set


@[main]
private lemma finset
  [DecidableEq ι]
  {A B : Finset ι}
  {x : ι} :
-- imply
  x ∈ A ↔ x ∈ A ∩ B ∨ x ∈ A \ B := by
-- proof
  have := EqUnionInter__SDiff.finset (s := A) (t := B)
  have := IffMemS.of.Eq.finset this x
  rw [Mem_Union.is.OrMemS.finset] at this
  rw [Iff.comm]
  assumption


@[main]
private lemma main
  {A B : Set α}
  {x : α} :
-- imply
  x ∈ A ↔ x ∈ A ∩ B ∨ x ∈ A \ B := by
-- proof
  have := EqUnionInter__SDiff (s := A) (t := B)
  have := IffMemS.of.Eq this x
  rw [Mem_Union.is.OrMemS] at this
  rw [Iff.comm]
  assumption


-- created on 2025-04-30
-- updated on 2025-05-01
