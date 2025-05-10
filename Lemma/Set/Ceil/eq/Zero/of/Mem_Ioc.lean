import sympy.sets.sets
import Lemma.Basic


@[main]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
  {x : α}
-- given
  (h : x ∈ Ioc (-1) 0) :
-- imply
  ⌈x⌉ = 0 := by
-- proof
  let ⟨h₀, h₁⟩ := h
  apply Int.ceil_eq_iff.mpr
  constructor <;>
  ·
    norm_num
    assumption


-- created on 2025-03-02
