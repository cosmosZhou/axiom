import Lemma.Tensor.Eq.is.EqArgsS
open Tensor


@[main]
private lemma main
  [Inhabited α]
  {a b : Tensor α s}
-- given
  (h : a = b) :
-- imply
  a.args = b.args :=
-- proof
  Eq.is.EqArgsS.mp h


-- created on 2025-05-06
