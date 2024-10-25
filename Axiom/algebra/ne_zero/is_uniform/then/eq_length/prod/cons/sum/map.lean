import Mathlib.Tactic
import Axiom.sympy.tensor.Tensor

import Axiom.algebra.length.join.to.sum.map
import Axiom.algebra.prod.cons.to.mul.prod
import Axiom.algebra.prod.to.mul.prod
import Axiom.algebra.is_uniform.then.is_uniform.map
import Axiom.algebra.map.map.to.map.comp
import Axiom.algebra.is_uniform.then.all.eq
import Axiom.algebra.headD.map.fn.to.fn.headD
import Axiom.algebra.ne_zero.then.eq.headD
import Axiom.algebra.ne_zero.then.eq.headD.map
import Axiom.algebra.sum.map.fn.mul.to.dot.map.fn
import Axiom.algebra.is_uniform.then.eq_dot.mul.sum

namespace algebra.ne_zero.is_uniform.then.eq_length.prod.cons.sum


theorem map
  {s : List (Tensor α)}
-- given
  (h1 : s.length ≠ 0)
  (h2: s.map (fun x => x.shape.tail) is uniform) :
-- imply
  let head_dimension := (s.map fun t => t.shape.headD 1).sum
  let tail_dimension := s[0].shape.tail
  let shape := head_dimension :: tail_dimension
  let args := (s.map (fun t => t.args)).join
  shape.prod = args.length := by
-- proof

  let head_dimension := (s.map (fun t => t.shape.headD 1)).sum
  let tail_dimension := s[0].shape.tail
  let shape := head_dimension :: tail_dimension
  let args := (s.map (fun t => t.args)).join


  have h_eq_map : s.map (fun t => t.args.length) = s.map (fun t => t.shape.prod) := by
    congr
    apply funext
    intro t
    exact t.precondition.symm

  have h_is_uniform : (s.map fun x => x.shape.tail).map (fun x => x.prod) is uniform := by
    apply algebra.is_uniform.then.is_uniform.map h2 (fun x => x.prod)

  have h_eq_map_map : (s.map fun x => x.shape.tail).map (fun x => x.prod) = s.map (fun x => x.shape.tail.prod) := by
    apply algebra.map.map.to.map.comp

  have h_is_uniform : s.map (fun x => x.shape.tail.prod) is uniform := by
    rw [h_eq_map_map] at h_is_uniform
    exact h_is_uniform

  have h_dot : (s.map fun t => t.shape.headD 1 * t.shape.tail.prod).sum = (s.map fun t => t.shape.headD 1).dot (s.map (fun t => t.shape.tail.prod)) := algebra.sum.map.fn.mul.to.dot.map.fn

  have h_eq_dot: (s.map fun t => t.shape.headD 1).dot (s.map (fun t => t.shape.tail.prod)) = (s.map fun t => t.shape.headD 1).sum * ((s.map fun t => t.shape.tail.prod).headD 0) := algebra.is_uniform.then.eq_dot.mul.sum h_is_uniform

  have h_eq_s_0_map : (s.map fun t => t.shape.tail.prod).headD 0 = tail_dimension.prod := algebra.ne_zero.then.eq.headD.map h1

  have h_eq_dot: (s.map fun t => t.shape.headD 1).dot (s.map (fun t => t.shape.tail.prod)) = head_dimension * tail_dimension.prod := by
    rw [h_eq_dot]
    rw [h_eq_s_0_map]

  have h_eq : (s.map fun t => t.shape.headD 1 * t.shape.tail.prod).sum = head_dimension * tail_dimension.prod := by
    rw [h_dot, h_eq_dot]

  have h_eq_mul : s.map (fun t => t.shape.prod) = s.map (fun t => t.shape.headD 1 * t.shape.tail.prod) := by
    congr
    apply funext
    intro t
    apply algebra.prod.to.mul.prod

  have h_eq : (s.map fun t => t.shape.prod).sum = head_dimension * tail_dimension.prod := by
    rw [h_eq_mul, h_eq]

  have h_eq : (s.map fun t => t.args.length).sum = head_dimension * tail_dimension.prod := by
    rw [h_eq_map, h_eq]

  have h_eq_map_map : (s.map (fun t => t.args)).map (fun s => s.length) = s.map fun t => t.args.length := by
    simp only [algebra.map.map.to.map.comp]
    apply congr_arg
    rfl

  have h_eq : ((s.map fun t => t.args).map fun s => s.length).sum = head_dimension * tail_dimension.prod := by
    rw [h_eq_map_map, h_eq]

  have h_eq_prod : shape.prod = head_dimension * tail_dimension.prod := by
    apply algebra.prod.cons.to.mul.prod

  have h : args.length = ((s.map fun t => t.args).map fun s => s.length).sum := algebra.length.join.to.sum.map
  have h : shape.prod = args.length := by
    rw [h_eq_prod, h_eq.symm, h]

  exact h

end algebra.ne_zero.is_uniform.then.eq_length.prod.cons.sum
open algebra.ne_zero.is_uniform.then.eq_length.prod.cons.sum
