import sympy.polys.polyroots
import Lemma.Basic


@[main]
private lemma main
  {x : ℂ} :
-- imply
  x = (∛x)³ := by
-- proof
  simp [Root.cubic]


-- created on 2024-07-01
