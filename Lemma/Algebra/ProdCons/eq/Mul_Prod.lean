import Lemma.Basic


@[main]
private lemma main
  [Monoid M]
  {l : List M} {a : M} :
-- imply
  (a :: l).prod = a * l.prod :=
-- proof
  List.prod_cons


-- created on 2024-07-01
