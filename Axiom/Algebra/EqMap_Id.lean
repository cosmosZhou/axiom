import stdlib.List.Vector
import Axiom.Basic


@[main]
private lemma main
  {s : List.Vector α n} :
-- imply
  s.map (fun x => x) = s := by
-- proof
  apply List.Vector.map_id


-- created on 2024-07-01
