import Axiom.Logic.Bool.eq.MulBoolS.of.Imp
import Axiom.Logic.Imp.of.Bool.eq.MulBoolS
open Logic


@[main]
private lemma main
  [Decidable p]
  [Decidable q] :
-- imply
  p → q ↔ Bool.toNat p = Bool.toNat p * Bool.toNat q := 
-- proof
  ⟨Bool.eq.MulBoolS.of.Imp, Imp.of.Bool.eq.MulBoolS⟩


-- created on 2025-04-20
