import Lemma.Algebra.Eq_Add.of.EqSub
import Lemma.Algebra.EqSub.of.Eq_Add
open Algebra


@[main]
private lemma left
  [AddCommGroup α]
  {x y d : α} :
-- imply
  y - d = x ↔ y = d + x:=
-- proof
  ⟨Eq_Add.of.EqSub.left, EqSub.of.Eq_Add.left⟩


@[main]
private lemma main
  [AddGroup α]
  {x y d : α} :
-- imply
  y - x = d ↔ y = d + x:=
-- proof
  ⟨Eq_Add.of.EqSub, EqSub.of.Eq_Add⟩


-- created on 2025-04-26
