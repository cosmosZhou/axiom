import sympy.tensor.tensor
import Lemma.Basic


@[main]
private lemma main
  [Mul α]
  {a b : Tensor α s} :
-- imply
  a * b = ⟨a.args.val.zipWith HMul.hMul b.args.val, by simp [Tensor.args]⟩ := by
-- proof
  rfl


-- created on 2025-05-02
