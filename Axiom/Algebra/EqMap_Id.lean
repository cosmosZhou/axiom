import Axiom.Basic


@[simp, main]
private lemma main
  {s : Vector α n} :
-- imply
  s.map (fun x => x) = s := by
-- proof
  apply Mathlib.Vector.map_id


-- created on 2024-07-01
