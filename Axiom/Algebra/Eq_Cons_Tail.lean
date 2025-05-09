import stdlib.List.Vector
import Axiom.Algebra.Eq_Cons_Tail.of.Ne_0
import Axiom.Algebra.EqValS.of.Eq
open Algebra


@[main]
private lemma main
-- given
  (v : List.Vector α (Nat.succ n)) :
-- imply
  v = v[0] ::ᵥ v.tail := by
-- proof
  let ⟨v, _⟩ := v
  match v with
  | [] =>
    contradiction
  | v₀ :: tail =>
    constructor


-- created on 2025-05-08
