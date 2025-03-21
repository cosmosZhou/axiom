open Lean

inductive Constant where
  | True
  | False
  | Infinity
  | NegativeInfinity
  | Infinitesimal
  | NegativeInfinitesimal
  | NaN
  | EmptySet
  | UniversalSet
  | EmptyList
  | Pi
  | ImaginaryUnit
  | Nat
  | Int
  | Rational
  | Real
  | Complex
  | true
  | false
  | natVal (val : Nat)
  | ident (name : Name)
  deriving Repr, BEq, Inhabited


def Constant.toString : Constant → String
  | True => "True"
  | False => "False"
  | Infinity => "Infinity"
  | NegativeInfinity => "NegativeInfinity"
  | Infinitesimal => "0⁺"
  | NegativeInfinitesimal => "0⁻"
  | NaN => "NaN"
  | EmptySet => "∅"
  | UniversalSet => "UniversalSet"
  | EmptyList => "[]"
  | Pi => "π"
  | ImaginaryUnit => "ImaginaryUnit"
  | Nat => "ℕ"
  | Int => "ℤ"
  | Rational => "ℚ"
  | Real => "ℝ"
  | Complex => "ℂ"
  | true => "true"
  | false => "false"
  | natVal val => s!"{val}"
  | ident name => name.toString


instance : ToString Constant where
  toString := Constant.toString


def Constant.toLatex : Constant → String
  | True => "\\top"
  | False => "\\bot"
  | Infinity => "\\infty"
  | NegativeInfinity => "-\\infty"
  | Infinitesimal => "0^+"
  | NegativeInfinitesimal => "0^-"
  | NaN => "\\mathrm{NaN}"
  | EmptySet => "\\emptyset"
  | UniversalSet => "\\mathbb{U}"
  | EmptyList => "[]"
  | Pi => "\\pi"
  | ImaginaryUnit => "\\color{blue}\\text{I}"
  | Nat => "\\mathbb{N}"
  | Int => "\\mathbb{Z}"
  | Rational => "\\mathbb{Q}"
  | Real => "\\mathbb{R}"
  | Complex => "\\mathbb{C}"
  | true => "true"
  | false => "false"
  | natVal val => s!"{val}"
  | ident name => name.toString
