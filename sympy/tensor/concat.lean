import sympy.tensor.Tensor
import Axiom.Algebra.Eq_Length_ProdConsSumMap.of.NeLength_0.IsConstantMap

-- https://pytorch.org/docs/stable/generated/torch.concat.html
-- here, we assume that torch.concat is only called with dim = 0 with torch.cat
def concat
  (s : List (Tensor α))
  (h: s.map (fun x => x.shape.tail) is constant) :
  Tensor α :=
  if h_ne_zero: s.length ≠ 0 then
    ⟨
      (s.map (fun t => t.shape.headD 1)).sum :: s[0].shape.tail,
      ⟨
        (s.map (fun t => t.args.val)).join,
        (Algebra.Eq_Length_ProdConsSumMap.of.NeLength_0.IsConstantMap h_ne_zero h).symm
      ⟩
    ⟩
  else
    default


-- https://pytorch.org/docs/stable/generated/torch.cat.html
-- def cat
--   (args : List (Tensor α))
--   (dim : ℕ)
--   (h: args.map (λ x => x.shape.eraseIdx dim) |>.) :
--   Tensor α :=
--   match axis with
--   | 0 => BlockMatrix_0 args h
--   | n + 1 =>
--   match n with
--   | 0 => BlockMatrix_1 args h
--   | n + 1 => _


-- def concat
