import Lemma.Tensor.Eq.is.EqArgsS
open Tensor


@[main]
private lemma main
  [Inhabited α]
  {a b : Tensor α s}
-- given
  (h : a.args = b.args) :
-- imply
  a = b :=
-- proof
  Eq.is.EqArgsS.mpr h


-- created on 2025-05-06
