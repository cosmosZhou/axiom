import sympy.polys.domains
import Axiom.Basic


@[main]
private lemma main
  [IntegerRing Z]
  {n d : Z} :
-- imply
  n = n / d * d + n % d :=
-- proof
  IntegerRing.div_add_mod


-- created on 2025-03-15
-- updated on 2025-03-16
