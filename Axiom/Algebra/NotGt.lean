import Axiom.Basic


@[main]
private lemma main
  [Preorder α]
  {a : α} :
-- imply
  ¬(a > a) :=
-- proof
  gt_irrefl a


-- created on 2025-03-27
