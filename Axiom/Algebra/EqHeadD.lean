import stdlib.List.Vector
import Axiom.Basic


@[main]
private lemma main
  {s : List.Vector α 0}
  {default : α} :
-- imply
  s.headD default = default := by
-- proof
  match s with
  | .nil => rfl


-- created on 2024-07-01
