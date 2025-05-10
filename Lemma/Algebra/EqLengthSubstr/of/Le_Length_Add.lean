import stdlib.List
import Lemma.Algebra.Add.comm
import Lemma.Algebra.LeSubS.of.Le
open Algebra


@[main]
private lemma main
  {s : List α}
  {i n : Nat}
-- given
  (h : i + n ≤ s.length) :
-- imply
  (s.substr i n |>.length) = n := by
-- proof
  simp [List.substr]
  have h'' : i + n - i ≤ s.length - i := LeSubS.of.Le.nat h i
  rw [Add.comm] at h''
  rw [Nat.add_sub_cancel] at h''
  exact h''


-- created on 2024-07-01
-- updated on 2025-03-31
