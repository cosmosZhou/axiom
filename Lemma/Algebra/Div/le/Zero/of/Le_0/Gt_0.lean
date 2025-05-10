import Lemma.Algebra.Eq.ou.Lt.of.Le
import Lemma.Algebra.Le.of.Lt
import Lemma.Algebra.Div.lt.Zero.of.Lt_0.Gt_0
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {x y : α}
-- given
  (h₀ : x ≤ 0)
  (h₁ : y > 0) :
-- imply
  x / y ≤ 0 := by
-- proof
  cases' Eq.ou.Lt.of.Le h₀ with hx hx
  ·
    simp_all
  ·
    apply Le.of.Lt
    apply Div.lt.Zero.of.Lt_0.Gt_0 hx h₁


-- created on 2025-05-05
