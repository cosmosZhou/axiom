import Axiom.Basic


@[simp, main]
private lemma main
  {s : Vector α 0}
  {default : α} :
-- imply
  s.headD default = default := by
-- proof
  match s with
  | .nil => rfl


-- created on 2024-07-01
