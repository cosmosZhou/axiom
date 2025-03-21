import Axiom.Basic


@[main]
private lemma main
  {a b : α}
  {p : α → Prop}
-- given
  (h0 : a = b)
  (h1 : p a) :
-- imply
  p b := by
-- proof
  exact h0 ▸ h1


-- created on 2025-01-12
