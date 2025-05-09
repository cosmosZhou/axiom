import Lean
open Lean (Macro explicitBinders)

syntax "∀" ident "|" term ", " term : term
macro_rules
  | `(∀ $x | $cond, $body) => `(∀ $x, $cond → $body)


syntax "∀" ident "∈" term "|" term ", " term : term
macro_rules
  | `(∀ $x ∈ $domain | $cond, $body) => `(∀ $x, $x ∈ $domain → $cond → $body)


syntax "∃" explicitBinders "|" term ", " term : term
macro_rules
  | `(∃ $x | $cond, $body) => `(∃ $x, $cond ∧ $body)


syntax "∃" explicitBinders "∈" term "|" term ", " term : term
macro_rules
  | `(∃ $x ∈ $domain | $cond, $body) => do
    let `(explicitBinders| $xIdent:ident) := x | Macro.throwError "expected explicit binders"
    `(∃ $x, $xIdent ∈ $domain ∧ $cond ∧ $body)
