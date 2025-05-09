import Axiom.Basic


@[main]
private lemma main
  [CommSemigroup G]
  (a b c : G) :
-- imply
  a * (b * c) = b * (a * c) :=
-- proof
  mul_left_comm a b c


-- created on 2025-03-23
