import Axiom.Logic.Imp.of.Or_Not
import Axiom.Logic.NotOr.is.AndNotS
import Axiom.Logic.NotAnd.is.OrNotS
import Axiom.Logic.IffNotNot
import Axiom.Logic.Or_Not.of.Imp
import Axiom.Logic.And_And.is.AndAnd
import Axiom.Logic.AndOr.is.OrAndS
import Axiom.Logic.OrAndS.of.And_Or
import Axiom.Logic.AndAnd.is.And_And
import Axiom.Logic.Or_Not.is.NotAndNot
open Logic


@[main]
private lemma main
-- given
  (h₀ : p₀ → q₀)
  (h₁ : p₁ → q₁) :
-- imply
  p₀ ∨ p₁ → q₀ ∨ q₁ := by
-- proof
  apply Imp.of.Or_Not
  rw [NotOr.is.AndNotS]
  by_contra h
  rw [NotOr.is.AndNotS] at h
  rw [NotAnd.is.OrNotS] at h
  rw [IffNotNot, IffNotNot] at h
  rw [NotOr.is.AndNotS] at h
  have h₀ := Or_Not.of.Imp h₀
  have := And.intro h₀ h
  rw [And_And.is.AndAnd] at this
  rw [And_And.is.AndAnd] at this
  rw [AndOr.is.OrAndS] at this
  simp at this
  have := OrAndS.of.And_Or this
  rw [And.comm (b := p₀)] at this
  rw [And_And.is.AndAnd] at this
  rw [And_And.is.AndAnd] at this
  simp at this
  rw [AndAnd.is.And_And] at this
  let ⟨_, h_And⟩ := this
  have := Or_Not.of.Imp h₁
  have := And.intro h_And this
  rw [Or_Not.is.NotAndNot] at this
  let ⟨h_And, h_Not⟩ := this
  contradiction


-- created on 2025-04-11
-- updated on 2025-04-12
