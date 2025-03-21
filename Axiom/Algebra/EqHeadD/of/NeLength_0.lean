import Axiom.Basic


@[main]
private lemma main
  {s : List α}
  {default : α}
-- given
  (h : s.length ≠ 0) :
-- imply
  s.headD default = s[0] := by
-- proof
  cases s with
  | nil =>
    contradiction
  | cons hd tl =>
    simp


-- created on 2024-07-01
