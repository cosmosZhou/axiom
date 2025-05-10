import Lemma.Logic.NotAll_Not.of.Any
import Lemma.Logic.Any.of.NotAll_Not
open Logic


@[main]
private lemma finset
  {p : ι → Prop}
  {s : Finset ι} :
-- imply
  (∃ x : s, p x) ↔ ¬∀ x : s, ¬p x :=
-- proof
  ⟨NotAll_Not.of.Any.finset, Any.of.NotAll_Not.finset⟩


@[main]
private lemma main
  {p : α → Prop} :
-- imply
  (∃ x : α, p x) ↔ ¬∀ x : α, ¬p x :=
-- proof
  ⟨NotAll_Not.of.Any, Any.of.NotAll_Not⟩


-- created on 2024-07-01
