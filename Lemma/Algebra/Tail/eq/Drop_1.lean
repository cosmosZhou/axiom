import stdlib.Slice
import Lemma.Basic


/--
For any list `s`, taking the tail of `s` is equivalent to dropping the first element of `s`.
This equivalence allows interchangeable use of `tail` and `drop 1` in contexts involving list operations,
facilitating proof simplification and code refactoring.
-/
@[main]
private lemma main
  {s : List α} :
-- imply
  s.tail = s.drop 1 := by
-- proof
  simp


-- created on 2025-05-05
