import Mathlib.Tactic
import Axiom.sympy.tensor.Tensor
import Axiom.algebra.ne_zero.is_uniform.then.eq_length.prod.cons.sum.map
set_option linter.unusedVariables false


-- https://pytorch.org/docs/stable/generated/torch.concat.html
-- here, we assume that torch.concat is only called with dim = 0 with torch.cat
def concat
  (s : List (Tensor α))
  (h: s.map (fun x => x.shape.tail) is uniform):
  Tensor α :=
  if h_ne_zero: s.length ≠ 0 then
    let head_dimension := (s.map (fun t => t.shape.headD 1)).sum
    let tail_dimension := s[0].shape.tail

    let shape := head_dimension :: tail_dimension
    let args := (s.map (fun t => t.args)).join
    let precondition : shape.prod = args.length := by
      apply algebra.ne_zero.is_uniform.then.eq_length.prod.cons.sum.map h_ne_zero h
    ⟨shape, args, precondition⟩
  else
    default


-- https://pytorch.org/docs/stable/generated/torch.cat.html
-- def cat
--   (args : List (Tensor α))
--   (dim : ℕ)
--   (h: args.map (λ x => x.shape.eraseIdx dim) |>.):
--   Tensor α :=
--   match axis with
--   | 0 => BlockMatrix_0 args h
--   | n + 1 =>
--   match n with
--   | 0 => BlockMatrix_1 args h
--   | n + 1 => _


-- def concat
