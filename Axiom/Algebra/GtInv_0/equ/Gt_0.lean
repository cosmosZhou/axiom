import Axiom.Basic


@[simp, main]
private lemma main
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  {x : α} :
-- imply
  x⁻¹ > 0 ↔ x > 0 :=
-- proof
  inv_pos


-- created on 2024-11-25
