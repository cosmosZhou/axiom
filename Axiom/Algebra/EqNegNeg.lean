import Axiom.Basic
open Algebra


@[main]
private lemma main
  [InvolutiveNeg α]
  {x : α} :
-- imply
  - -x = x :=
-- proof
  neg_neg x


-- created on 2025-03-16
