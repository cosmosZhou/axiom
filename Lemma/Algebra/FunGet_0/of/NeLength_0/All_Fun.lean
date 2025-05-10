import Lemma.Algebra.All_Eq_HeadD.of.IsConstant
import Lemma.Algebra.IsConstantTail.of.IsConstant
import Lemma.Set.Expr.mem.Cons
import Lemma.Algebra.Eq_Cons_Tail.of.Ne_0
open Algebra


@[main]
private lemma main
  {s : List α}
  {p: α → Prop}
-- given
  (h_ne: s.length ≠ 0)
  (h_all : ∀ t ∈ s, p t) :
-- imply
  p s[0] := by
-- proof
  apply h_all s[0]
  have h_eq := Eq_Cons_Tail.of.Ne_0 h_ne
  have h_in : s[0] ∈ s[0] :: s.tail := Set.Expr.mem.Cons
  rw [h_eq.symm] at h_in
  exact h_in


-- created on 2024-07-01
