import stdlib.List.Vector
import Lemma.Basic


@[main]
private lemma main
  [Add α] [Zero α]
  {s : List.Vector α 0} :
-- imply
  s.sum = 0 := by
-- proof
  match s with
  | ⟨v, property⟩ =>
    simp [List.Vector.sum] at property
    simp [List.Vector.sum, property]


-- created on 2024-07-01
