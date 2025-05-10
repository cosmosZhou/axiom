import Lemma.Basic


@[main]
private lemma main
  {α : Sort u}
  {β : Sort v}
  {a₁ a₂ : α}
-- given
  (h : a₁ = a₂)
  (f : α → β) :
-- imply
  f a₁ = f a₂ :=
-- proof
  congrArg f h


-- created on 2025-03-04
