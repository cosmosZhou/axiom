import Axiom.Set.EqUnionSDiff__Inter
import Axiom.Set.Union.comm
open Set


@[main]
private lemma finset
  [DecidableEq ι]
  {s t : Finset ι} :
-- imply
  s ∩ t ∪ s \ t = s := by
-- proof
  have := EqUnionSDiff__Inter.finset (s := s) (t := t)
  rw [Union.comm.finset] at this
  assumption


@[main]
private lemma main
  {s t : Set α} :
-- imply
  s ∩ t ∪ s \ t = s :=
-- proof
  Set.inter_union_diff s t


-- created on 2025-04-30
