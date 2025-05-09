import Axiom.Basic


@[main]
private lemma left
  [CommGroup G]
  (a b : G) :
-- imply
  a * b / a = b :=
-- proof
  mul_div_cancel_left a b


@[main]
private lemma main
  [Group G]
  (a b : G) :
-- imply
  a * b / b = a :=
-- proof
  mul_div_cancel_right a b


-- created on 2025-03-30
