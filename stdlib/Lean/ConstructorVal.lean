import Lean
open Lean

def Lean.ConstructorVal.toJson (ctor : ConstructorVal) : Json :=
  Json.mkObj [
    ("name", ctor.name.toString),
    ("numParams", ctor.numParams),
    ("numFields", ctor.numFields),
    ("isUnsafe", ctor.isUnsafe)
  ]

instance : ToJson ConstructorVal where
  toJson := ConstructorVal.toJson

def Lean.ConstructorVal.toString (ctor : ConstructorVal) : String :=
  ToString.toString (toJson ctor)


instance : ToString ConstructorVal where
  toString := ConstructorVal.toString
