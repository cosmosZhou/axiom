import sympy.polys.domains
import Axiom.Algebra.Mul.comm
open Algebra


@[main]
private lemma main
  [IntegerRing Z]
  {n d : Z} :
-- imply
  n = n / d * d + n % d :=
-- proof
  IntegerRing.div_add_mod


-- created on 2025-03-15
-- updated on 2025-03-21
