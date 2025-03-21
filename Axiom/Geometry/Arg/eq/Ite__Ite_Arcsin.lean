import Axiom.Basic


@[main]
private lemma main
  {z : ℂ} :
-- imply
  arg z =
    if re z ≥ 0 then
      arcsin (im z / abs z)
    else if im z ≥ 0 then
      arcsin (im (-z) / abs z) + π
    else
      arcsin (im (-z) / abs z) - π := by
-- proof
  rw [arg]


-- created on 2025-01-06
