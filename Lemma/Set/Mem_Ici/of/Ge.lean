import sympy.sets.sets
import Lemma.Basic


@[main]
private lemma main
  [Preorder α]
  {x a : α}
-- given
  (h : x ≥ a) :
-- imply
  x ∈ Ici a :=
-- proof
  -- By definition, `x ∈ Ici a` is equivalent to `x ≥ a`.
  -- Given the hypothesis `h : x ≥ a`, we can directly conclude the proof.
  UpperSet.mem_Ici_iff.mpr h


-- created on 2025-04-27
