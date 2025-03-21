import Axiom.Algebra.All_EqFunS.of.All_Eq
import Axiom.Algebra.TailCons.eq.Tail
import Axiom.Algebra.IsConstant.of.All_Eq


@[main]
private lemma main
  {s : Vector α n}
-- given
  (h: s.val is constant) :
-- imply
  s is constant := by
-- proof
  exact h


-- created on 2024-07-01
