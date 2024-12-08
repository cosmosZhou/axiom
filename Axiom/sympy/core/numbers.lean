import Axiom.Basic


class Root (T : Type _) where
  sqrt : T → T
  cubic : T → T
  quartic : T → T


notation:max "√" x:max => Root.sqrt x
notation:max "∛" x:max => Root.cubic x
notation:max "∜" x:max => Root.quartic x


noncomputable instance : Root Real where
  sqrt := Real.sqrt
  cubic x := x ^ (3:ℝ)⁻¹
  quartic x := x ^ (4:ℝ)⁻¹


noncomputable instance : Root Complex where
  sqrt x := x ^ (2:ℂ)⁻¹
  cubic x := x ^ (3:ℂ)⁻¹
  quartic x := x ^ (4:ℂ)⁻¹


notation:max x "²" => x ^ 2  -- square
notation:max x "³" => x ^ 3  -- cube
notation:max x "⁴" => x ^ 4  -- tesseract
