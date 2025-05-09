import Axiom.Basic


@[main]
private lemma nat
  [AddZeroClass R]
  [AddMonoidWithOne R]
  [Nat.AtLeastTwo a] :
-- imply
  (Nat.cast 0 : R) + OfNat.ofNat a = OfNat.ofNat a := by
-- proof
  simp [zero_add]


@[main]
private lemma main
  [AddZeroClass R]
  {a : R} :
-- imply
  0 + a = a := by
-- proof
  rw [zero_add]


-- created on 2024-07-01
-- updated on 2025-04-26
