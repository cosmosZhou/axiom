import stdlib.List.Vector


def Lamda (n : ℕ) (f : ℕ → α) : List.Vector α n :=
  match n with
  | 0 => .nil
  | n + 1 => f 0 ::ᵥ (Lamda n (fun i => f (i + 1)))


syntax "[" ident "<" term "]" term:67 : term
macro_rules
  | `([$x < $n] $body) => `(Lamda $n fun $x => $body)
