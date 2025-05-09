import stdlib.List.Vector
import Axiom.Basic


@[main]
private lemma main
  [Inhabited α]
  {v : List.Vector α (m * n)}
  {i : Fin m}
  {j : Fin n} :
-- imply
  v[i * n + j] = v.unflatten[i, j] := by
-- proof
  sorry


-- created on 2025-05-07
