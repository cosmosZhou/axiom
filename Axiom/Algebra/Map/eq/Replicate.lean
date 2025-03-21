import Axiom.Algebra.GetMap.eq.FunGet
open Mathlib Algebra


@[main]
private lemma main
  {s : Vector α n}
  {default : α} :
-- imply
  (s.map fun _ => default) = Vector.replicate n default := by
-- proof
  apply Mathlib.Vector.ext
  intro i
  simp [GetMap.eq.FunGet]


-- created on 2024-07-01
