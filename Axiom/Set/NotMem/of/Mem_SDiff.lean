import Axiom.Basic


@[main]
private lemma main
  {s S : Set α}
  {e : α}
-- given
  (h : e ∈ S \ s) :
-- imply
  e ∉ s := by
-- proof
  exact h.right


-- created on 2025-04-05
