import sympy.polys.polyroots
import Axiom.Basic


@[main]
private lemma main
  {x : ℂ} :
-- imply
  (√x)² = x := by
-- proof
  simp [Root.sqrt]


-- created on 2024-07-01
