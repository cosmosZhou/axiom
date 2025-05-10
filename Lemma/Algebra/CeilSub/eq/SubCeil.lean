import Lemma.Basic


@[main]
private lemma nat
  [LinearOrderedRing α]
  [FloorRing α]
  {x : α}
  {d : ℕ} :
-- imply
  ⌈x - d⌉ = ⌈x⌉ - d := by
-- proof
  simp


@[main]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
  {x : α}
  {d : ℤ} :
-- imply
  ⌈x - d⌉ = ⌈x⌉ - d :=
-- proof
  Int.ceil_sub_int x d




-- created on 2025-05-04
