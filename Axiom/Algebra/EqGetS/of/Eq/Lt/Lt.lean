import stdlib.List
import Axiom.Basic


@[main]
private lemma main
  {a b : List α}
  {i : ℕ}
-- given
  (h₀ : i < a.length)
  (h₁ : i < b.length)
  (h : a = b) :
-- imply
  a[i] = b[i] := by
-- proof
  simp [h]


-- created on 2025-05-09
