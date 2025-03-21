import Axiom.Basic


@[main]
private lemma main
  (z : ℂ) :
-- imply
  arg z ∈ Ioc (-π) π :=
-- proof
  Complex.arg_mem_Ioc z


-- created on 2025-01-05
