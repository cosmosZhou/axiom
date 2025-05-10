import stdlib.List.Vector
import Lemma.Basic


@[main]
private lemma main
-- given
  (f : α → β)
  (a : α)
  (l : List α) :
-- imply
  (a :: l).map f = f a :: l.map f :=
-- proof
  List.map_cons f a l


-- created on 2025-05-08
