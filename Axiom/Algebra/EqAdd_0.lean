import Axiom.Basic


@[main]
private lemma nat
  [AddZeroClass R]
  [AddMonoidWithOne R]
  [Nat.AtLeastTwo a] :
-- imply
  OfNat.ofNat a + (Nat.cast 0 : R)  = OfNat.ofNat a := by
-- proof
  simp [add_zero]


@[main]
private lemma main
  [AddZeroClass R]
  {a : R} :
-- imply
  a + 0 = a := by
-- proof
  rw [add_zero]


-- created on 2024-07-01
