import Axiom.Algebra.Add.comm
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
  have h'' : i + n - i ≤ s.length - i := Nat.sub_le_sub_right h i
  rw [Add.comm] at h''
  rw [Nat.add_sub_cancel] at h''
  exact h''


-- created on 2024-07-01
