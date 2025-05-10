import Lemma.Basic


@[main]
private lemma main
  [MulZeroClass α]
  {a : List α}
-- given
  (h : a.length = l) :
-- imply
  List.zipWith HMul.hMul a (List.replicate l 0) = List.replicate l 0 := by
-- proof
  induction a generalizing l with
  | nil =>
    simp_all
  | cons head tail ih =>
    match l with
    | .zero =>
      contradiction
    | .succ l =>
      simp_all [List.zipWith, List.replicate]


-- created on 2025-05-02
