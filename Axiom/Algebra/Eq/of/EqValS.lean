import Axiom.Basic


@[main]
private lemma main
  {s : Vector α n}
-- given
  (h: s.val = s'.val) :
-- imply
  s = s' := by
-- proof
  apply Mathlib.Vector.eq s s' h


-- created on 2024-07-01
