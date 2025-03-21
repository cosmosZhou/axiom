import Axiom.Basic


@[simp, main]
private lemma main
  {s : Vector α n}
  {default : α} :
-- imply
  (a ::ᵥ s).headD default = a := by
-- proof
  rfl


-- created on 2024-07-01
