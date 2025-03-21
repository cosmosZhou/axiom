import std.Basic
#eval mkCtorName ``Lean.BinderInfo

instance : ToString Lean.BinderInfo where
  toString := ctorName
