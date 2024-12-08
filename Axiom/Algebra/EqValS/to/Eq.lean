import Axiom.Basic
open Mathlib
namespace Algebra.EqValS.to

theorem Eq
  {s : Vector α n}
-- given
  (h: s.val = s'.val) :
-- imply
  s = s' := by
-- proof
  apply Vector.eq s s' h


end Algebra.EqValS.to

-- created on 2024-07-01
