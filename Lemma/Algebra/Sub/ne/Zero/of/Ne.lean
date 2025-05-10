import Lemma.Algebra.Eq.of.Sub.eq.Zero
import Lemma.Logic.NotNe.of.Eq
open Algebra Logic


@[main]
private lemma main
  [AddGroup α]
  {a b : α}
-- given
  (h : a ≠ b) :
-- imply
  a - b ≠ 0 := by
-- proof
  by_contra h'
  have := Eq.of.Sub.eq.Zero h'
  have := NotNe.of.Eq this
  contradiction


-- created on 2025-03-30
