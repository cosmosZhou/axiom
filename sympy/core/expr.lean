import sympy.Lean.Expr
import sympy.core.singleton
import std.Basic
import std.Name
import std.String
open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


structure Func where
  priority : Nat
  -- lean operator
  operator : String
  -- latex command
  command : String
deriving BEq, Repr, Inhabited


structure BinaryInfix where
  name : Name
deriving BEq, Repr


def BinaryInfix.func : BinaryInfix → Func
  | ⟨name⟩ =>
    match name with
    | `HAdd.hAdd => ⟨40, "+", "+"⟩ -- LAdd
    | `HSub.hSub => ⟨40, "-", "-"⟩  -- LSub
    | `HMul.hMul => ⟨43, "*", "\\cdot"⟩  -- LMul
    | `HPow.hPow => ⟨44, "^", "^"⟩  -- LPow
    | `HDiv.hDiv => ⟨43, "/", "\\frac"⟩  -- LDiv
    | `Rat.divInt => ⟨43, "/", "\\frac"⟩  -- LDiv
    | `HMod.hMod => ⟨43, "%%", "\\%%"⟩  -- LMod
    | `Union.union => ⟨33, "∪", "\\cup"⟩  -- L_cup
    | `Inter.inter => ⟨34, "∩", "\\cap"⟩  -- L_cap
    | `OPlus.f => ⟨45, "⊕", "\\oplus"⟩  -- L_oplus
    | `OTimes.f => ⟨46, "⊗", "\\otimes"⟩  -- L_otimes
    | `ODot.f => ⟨46, "⊙", "\\odot"⟩  -- L_odot
    | `Bullet.f => ⟨46, "•", "\\bullet"⟩  -- L_bullet
    | `Function.comp => ⟨40, "∘", "\\circ"⟩  -- L_circ
    | `List.cons => ⟨40, "::", "::"⟩  -- LConcat
    | `Mathlib.Vector.cons => ⟨40, "::ᵥ", "::_v"⟩  -- LVConcat
    | `Mathlib.Vector.dot => ⟨40, "⬝", "\\cdotp"⟩  -- L_cdotp
    | `LE.le => ⟨32, "≤", "\\le"⟩  -- L_le
    | `GE.ge => ⟨32, "≥", "\\ge"⟩  -- L_ge
    | `LT.lt => ⟨32, "<", "<"⟩  -- L_lt
    | `GT.gt => ⟨32, ">", ">"⟩  -- L_gt
    | `Eq => ⟨32, "=", "="⟩  -- LEq
    | `Ne => ⟨32, "≠", "\\ne"⟩ -- L_ne
    | `And => ⟨10, "∧", "\\land"⟩  -- L_land
    | `Or => ⟨9, "∨", "\\lor"⟩  -- L_lor
    | `Iff => ⟨8, "↔", "\\leftrightarrow"⟩  -- L_leftrightarrow
    | `Membership.mem
    | `List.Mem => ⟨39, "∈", "\\in"⟩  -- L_in ∋ \\ni
    | `HasSubset.Subset => ⟨20, "⊆", "\\subseteq"⟩  -- L_subset
    | `Superset => ⟨20, "⊇", "\\supseteq"⟩  -- L_supset
    | `Dvd.dvd => ⟨32, "∣", "\\mid"⟩  -- L_mid
    | _ => panic! s!"BinaryInfix.func : unknown operator {name}"


def BinaryInfix.isProp : BinaryInfix → Bool
  | ⟨name⟩ =>
    match name with
    | `LE.le
    | `GE.ge
    | `LT.lt
    | `GT.gt
    | `Eq
    | `Ne
    | `And
    | `Or
    | `Iff
    | `Membership.mem
    | `List.Mem
    | `HasSubset.Subset
    | `Superset
    | `Dvd.dvd => true
    | _ => false


structure UnaryPrefix where
  name : Name
deriving BEq, CtorName, Repr


def UnaryPrefix.func : UnaryPrefix → Func
  | ⟨name⟩ =>
    match name with
    | `Neg.neg => ⟨41, "-", "-"⟩  -- LNeg
    | `Not => ⟨38, "¬", "\\lnot"⟩  -- L_lnot
    | `Complex.ofReal => ⟨45, "↑", "\\uparrow"⟩  -- L_uparrow
    | `Nat.cast
    | `Int.cast => ⟨45, "↑", "\\uparrow"⟩  -- L_uparrow
    | `DFunLike.coe => ⟨45, "⇑", "\\Uparrow"⟩  -- LUparrow
    | `Real.sqrt => ⟨45, "√", "\\sqrt"⟩  -- LRealSqrt
    | `Root.sqrt => ⟨45, "√", "\\sqrt"⟩  -- L_sqrt
    | `OfNat.ofNat => ⟨80, "cast", ""⟩  -- L_cast
    | _ => panic! s!"UnaryPrefix.func : unknown operator {name}"


def UnaryPrefix.isProp : UnaryPrefix → Bool
  | ⟨`Not⟩ => true
  | _ => false


structure UnaryPostfix where
  name : Name
deriving BEq, Repr


def UnaryPostfix.func: UnaryPostfix → Func
  | ⟨name⟩ =>
    match name with
    | `Inv.inv => ⟨45, "⁻¹", "^{-1}"⟩
    | _ => panic! s!"UnaryPostfix.func : unknown operator {name}"


inductive ExprWithLimits where
  | L_sum
  | L_prod
  | L_int (name : Name)
  | L_bigcap (name : Name)
  | L_bigcup (name : Name)
  | L_lim (name : Name)
  | L_sup (name : Name)
  | L_inf (name : Name)
  | L_max (name : Name)
  | L_min (name : Name)
  | L_forall
  | L_exists
  | L_lambda
  | L_let
deriving BEq, Repr


def ExprWithLimits.func : ExprWithLimits → Func
  | L_sum  => ⟨33, "∑", "\\sum"⟩
  | L_prod => ⟨33, "∏", "\\prod"⟩
  | L_int _ => ⟨33, "∫", "\\int"⟩
  | L_bigcap _ => ⟨33, "⋂", "\\bigcap"⟩
  | L_bigcup _ => ⟨33, "⋃", "\\bigcup"⟩
  | L_lim _ => ⟨33, "lim", "\\lim"⟩
  | L_sup _ => ⟨33, "sup", "\\sup"⟩
  | L_inf _ => ⟨33, "inf", "\\inf"⟩
  | L_max _ => ⟨33, "max", "\\max"⟩
  | L_min _ => ⟨33, "min", "\\min"⟩
  | L_forall => ⟨20, "∀", "\\forall"⟩
  | L_exists => ⟨20, "∃", "\\exists"⟩
  | L_lambda => ⟨45, "fun", "\\operatorname{\\color{magenta}fun}"⟩
  | L_let => ⟨20, "let", "let"⟩


def ExprWithLimits.name : ExprWithLimits → Name
  | L_forall => .anonymous
  | L_exists => `Exists
  | L_sum => `Finset.sum
  | L_prod => `Finset.prod
  | L_int name
  | L_bigcap name
  | L_bigcup name
  | L_lim name
  | L_sup name
  | L_inf name
  | L_max name
  | L_min name
  | L_lambda
  | L_let => .anonymous


def Binder.func : Binder → Func
  | implicit => ⟨20, "{%s : %s}", "\\left\\lbrace %s : %s\\right\\rbrace"⟩
  | strictImplicit => ⟨20, "⦃%s : %s⦄", "⦃%s : %s⦄"⟩
  | instImplicit => ⟨20, "[%s]", "\\left[%s\\right]"⟩
  | given => ⟨20, "(%s : %s)", "\\left(%s : %s\\right)"⟩
  | default => ⟨20, "(%s : %s)", "\\left(%s : %s\\right)"⟩
  | contains => ⟨20, "%s ∈ %s", "{%s \\in %s}"⟩


structure Special where
  name : Name
deriving BEq, Repr


def Special.func : Special → Func
  | ⟨name⟩ =>
    match name with
    | .anonymous => ⟨45, "__call__", "__call__"⟩
    | `abs => ⟨33, "|%s|", "\\left|%s\\right|"⟩  -- LAbs
    | `Norm.norm => ⟨33, "‖%s‖", "\\left\\lVert%s\\right\\rVert"⟩  -- LNorm
    | `Int.ceil => ⟨45, "⌈%s⌉", "\\left\\lceil%s\\right\\rceil"⟩  -- LCeil
    | `Int.floor => ⟨45, "⌊%s⌋", "\\left\\lfloor%s\\right\\rfloor"⟩  -- LFloor
    | `ite => ⟨33, "ite", "ite"⟩  -- LITE
    | `Prod.mk => ⟨90, "⟨%s, %s⟩", "\\langle %s, %s \\rangle"⟩  -- LAngleBracket
    | `GetElem.getElem => ⟨90, "%s[%s]", "%s_%s"⟩  -- LGetElem
    | `Nat.ModEq => ⟨32, "%s ≡ %s [MOD %s]", "%s \\equiv %s\\ \\left[\\operatorname{MOD}\\ %s\\right]"⟩  -- L_equiv
    | .str _ "match_1" => ⟨33, "match", "match"⟩  -- L_match
    | _ => panic! s!"Special.func : unknown operator {name}"


inductive ExprWithAttr where
  | L_function (name : Name)
  | L_operatorname (name : Name)
  | LMethod (name : Name)
  | L_typeclass (name : Name)
  | LAttr (name : Name)
deriving BEq, Repr


def ExprWithAttr.func : ExprWithAttr → Func
  | L_function name =>
    let name := name.getLast.toString
    ⟨44, name, "\\" ++ name⟩
  | L_operatorname name =>
    let name := name.getLast.toString
    ⟨
      44,
      name,
      "\\operatorname{%s}".format name
    ⟩
  | LMethod name =>
    let name := name.getLast.toString
    ⟨44, s!"%s.{name} %s", s!"%s.{name}\\ %s"⟩
  | L_typeclass name =>
    let name := name.getLast.toString
    ⟨
      42,
      name,
      "\\operatorname{\\color{#770088}{%s}}".format name
    ⟩
  | LAttr name =>
    let name := name.getLast.toString
    ⟨90, s!".{name}", s!".{name}"⟩


def ExprWithAttr.name : ExprWithAttr → Name
  | L_function name
  | L_operatorname name
  | LMethod name
  | L_typeclass name
  | LAttr name => name


def ExprWithAttr.isProp : ExprWithAttr → Bool
  | .LAttr `IsConstant.is_constant => true
  | _ => false


inductive Operator where
  | BinaryInfix (op : BinaryInfix)
  | UnaryPrefix (op : UnaryPrefix)
  | UnaryPostfix (op : UnaryPostfix)
  | ExprWithLimits (op : ExprWithLimits)
  | Special (op : Special)
  | ExprWithAttr (op : ExprWithAttr)
deriving BEq, CtorName, Repr


def Operator.func : Operator → Func
  | BinaryInfix op => op.func
  | UnaryPrefix op => op.func
  | UnaryPostfix op => op.func
  | ExprWithLimits op => op.func
  | Special op => op.func
  | ExprWithAttr op => op.func


def Operator.priority : Operator → Nat :=
  Func.priority ∘ Operator.func


def Operator.operator : Operator → String :=
  Func.operator ∘ Operator.func


def Operator.name : Operator → Name
  | BinaryInfix op => op.name
  | UnaryPrefix op => op.name
  | UnaryPostfix op => op.name
  | ExprWithLimits op => op.name
  | Special op => op.name
  | ExprWithAttr op => op.name


instance : ToString Operator where
  toString := Operator.operator


def Operator.command : Operator → String :=
  Func.command ∘ Operator.func


inductive Expr where

  | nil

  | const (val : Constant)

  | sort (u : Level)

  | Symbol (name : Name) (type : Expr)

  | Basic (func : Operator) (args : List Expr)

  | Binder (binder : Binder) (binderName : Name) (binderType : Expr) (value : Expr)
deriving Inhabited, BEq, CtorName

def Expr.priority : Expr → Nat
  | nil => 0
  | sort ..
  | Symbol ..
  | const _ => 90
  | Basic op _ => op.priority
  | Binder binder _ _ _ => binder.func.priority


def Expr.isEmpty : Expr → Bool
  | nil => true
  | _ => false


def Expr.isTypeClass : Expr → Bool
  | Basic (.ExprWithLimits .L_forall) (.sort .zero :: _) => true
  | _ => false


def getExprMVarAssignment (mvarId : Lean.MVarId) : MetaM Lean.Expr := do
    if let some e ← Lean.getExprMVarAssignment? mvarId then
      return e
    if let some dAssign ← Lean.getDelayedMVarAssignment? mvarId then
      if let some e' ← Lean.getExprMVarAssignment? dAssign.mvarIdPending then
        let ctx := (← getMCtx).getDecl dAssign.mvarIdPending
        return ← withLCtx ctx.lctx ctx.localInstances do
          let mut e := e'
          let mut binderName := #[]
          let mut binderType := #[]
          for (i, fvar) in dAssign.fvars.mapIdx Prod.mk do
            if let .fvar fvarId := fvar then
              e ← e.subs fvarId i
              let name ←
                if let some decl ← fvarId.findDecl? then
                  pure decl.userName
                else
                  panic! s!"Expr.func.fvar : unknown free variable {fvarId.name}"
              binderName := binderName.push name
              binderType := binderType.push (← inferType fvar)

          e := Array.zip binderName binderType |>.foldl (init := e) fun e (name, type) =>
            .lam name type e .implicit
/-
          println! s!"getExprMVarAssignment :
e' = {e'}, e' = {← ppExpr e'}, e'.type = {← inferType e'}
e = {e}, e = {← ppExpr e}, e.type = {← inferType e}
dAssign.fvars = {dAssign.fvars}
"
-/
          pure e

    panic! s!"Expr.func.mvar.some : unknown metavariable {mvarId.name}"


inductive TreeNode where
  | Operator (op : Operator)
  | const (expr : Expr)


partial def Expr.func (e : Lean.Expr) (toExpr : Lean.Expr → MetaM Expr) (binders : List Expr) : MetaM TreeNode := do
  match e with
  | .bvar deBruijnIndex  =>
    return .const (binders.get! deBruijnIndex)

  | .fvar fvarId  =>
    if let some decl ← fvarId.findDecl? then
      let type := decl.type
      return .const (Symbol decl.userName (← toExpr type))
    else
      panic! s!"Expr.func.fvar : unknown free variable {fvarId.name}"

  | .mvar mvarId  =>
/-
    if e.toString == "" then
      println! s!"Expr.func.mvar :
e = {e}, e = {← ppExpr e}, e.type = {← inferType e}"
-/
    Expr.func (← getExprMVarAssignment mvarId) toExpr binders

  | .sort u =>
    return .const (sort u)

  | .const declName _  =>
    match declName with
    | `LE.le
    | `LT.lt
    | `GE.ge
    | `GT.gt
    | `Ne
    | `Eq
    | `HAdd.hAdd
    | `HSub.hSub
    | `HMul.hMul
    | `HPow.hPow
    | `HDiv.hDiv
    | `Rat.divInt
    | `HMod.hMod
    | `And
    | `Or
    | `Iff
    | `Membership.mem
    | `List.Mem
    | `Inter.inter
    | `Union.union
    | `Function.comp
    | `List.cons
    | `Mathlib.Vector.cons
    | `Mathlib.Vector.dot
    | `HasSubset.Subset
    | `Superset
    | `Dvd.dvd
    | `OPlus.f
    | `OTimes.f
    | `ODot.f
    | `Bullet.f =>
      return .Operator (.BinaryInfix ⟨declName⟩)

    | `Neg.neg
    | `Not
    | `Real.sqrt
    | `Root.sqrt
    | `Complex.ofReal
    | `Nat.cast
    | `Int.cast
    | `OfNat.ofNat
    | `DFunLike.coe =>
      return .Operator (.UnaryPrefix ⟨declName⟩)

    | `Inv.inv =>
      return .Operator (.UnaryPostfix ⟨declName⟩)

    | `Real.cos
    | `Real.sin
    | `Real.arccos
    | `Real.arcsin
    | `Complex.arg =>
      return .Operator (.ExprWithAttr (.L_function declName))

    | `List.length
    | `List.tail
    | `List.sum
    | `List.prod
    | `Prod.fst
    | `Prod.snd
    | `Mathlib.Vector.length
    | `Mathlib.Vector.head
    | `Mathlib.Vector.tail
    | `Mathlib.Vector.sum
    | `Mathlib.Vector.toList
    | `Nat.pred
    | `Nat.succ
    | `Complex.cos
    | `Complex.sin
    | `Complex.exp
    | `Complex.log
    | `IsConstant.is_constant
    | `Subtype.val
    | `Tensor.shape
    | `Tensor.args =>
      return .Operator (.ExprWithAttr (.LAttr declName))

    | `id
    | `Real.exp
    | `Complex.re
    | `Complex.im
    | `Complex.abs
    | `Complex.normSq
    | `Complex.cpow
    | `List.replicate
    | `Finset.range
    | `Set.Ioo
    | `Set.Ico
    | `Set.Iio
    | `Set.Icc
    | `Set.Iic
    | `Set.Ioc
    | `Set.Ici
    | `Set.Ioi
    | `Int.sign
    | `Mathlib.Vector.replicate =>
      return .Operator (.ExprWithAttr (.L_operatorname declName))

    -- instImplicit
    | `Set
    | `List
    | `Fin
    | `Finset
    | `OPlus
    | `OTimes
    | `ODot
    | `Bullet
    | `Mathlib.Vector
    | `Tensor =>
      return .Operator (.ExprWithAttr (.L_typeclass declName))

    | `abs             -- LAbs
    | `Norm.norm       -- LNorm
    | `Int.ceil        -- LCeil
    | `Int.floor       -- LFloor
    | `Prod.mk         -- LAngleBracket
    | `GetElem.getElem -- LGetElem
    | `ite             -- LITE
    | `Nat.ModEq =>    -- L_equiv
      return .Operator (.Special ⟨declName⟩)

    | `List.get
    | `List.map
    | `List.headD
    | `List.join
    | `Mathlib.Vector.get
    | `Mathlib.Vector.map
    | `Mathlib.Vector.headD
    | `Int.tdiv
    | `Int.tmod =>
      return .Operator (.ExprWithAttr (.LMethod declName))

    | `True =>
      return .const (const .True)
    | `False =>
      return .const (const .False)
    | `Infinity =>
      return .const (const .Infinity)
    | `NegativeInfinity =>
      return .const (const .NegativeInfinity)
    | `Infinitesimal =>
      return .const (const .Infinitesimal)
    | `NegativeInfinitesimal =>
      return .const (const .NegativeInfinitesimal)
    | `NaN =>
      return .const (const .NaN)
    | `EmptySet =>
      return .const (const .EmptySet)
    | `UniversalSet =>
      return .const (const .UniversalSet)
    | `Real.pi =>
      return .const (const .Pi)
    | `Complex.I =>
      return .const (const .ImaginaryUnit)
    | `Nat =>
      return .const (const .Nat)
    | `Int =>
      return .const (const .Int)
    | `Rational =>
      return .const (const .Rational)
    | `Real =>
      return .const (const .Real)
    | `List.nil =>
      return .const (const .EmptyList)
    | `Complex =>
      return .const (const .Complex)
    | `Complex.instZero =>
      return .const (const (.natVal 0))
    | `Bool.true =>
      return .const (const .true)
    | `Bool.false =>
      return .const (const .false)

    | `Finset.sum =>
      return .Operator (.ExprWithLimits .L_sum)
    | `Finset.prod =>
      return .Operator (.ExprWithLimits .L_prod)
    | `Exists =>
      return .Operator (.ExprWithLimits .L_exists)

    | .str _ "match_1" =>
      return .Operator (.Special ⟨declName⟩)

    | _ =>
      if Lean.isClass (← Lean.getEnv) declName || (← toExpr (← declName.toConstantInfo).type).isTypeClass then
        return .Operator (.ExprWithAttr (.L_typeclass declName))
      else
        -- println! s!"unknown constant {declName}"
        return .const nil

  | .app fn arg =>
    let op ← Expr.func fn toExpr binders
    match op with
    | .Operator func =>
/-
      if e.toString == "" then
        println! s!"Expr.func.app.Operator :
e = {e}, e = {← ppExpr e}
fn = {fn}, fn = {← ppExpr fn}
arg = {arg}, arg = {← ppExpr arg}
func = {func}
"
-/
      match func with
      | .ExprWithLimits .L_lambda =>
        return .Operator (.Special ⟨.anonymous⟩)

      | .UnaryPrefix ⟨`DFunLike.coe⟩ =>
        if arg.ctorName == "const" then
          let arg_func ← Expr.func arg toExpr binders
          match ← Expr.func arg toExpr binders with
          | .Operator (.UnaryPrefix _) =>
            return arg_func
          | _ =>
            return op
        else
          return op
      | _ =>
        return op
    | .const c =>
/-
      if e.toString == "" then
        println! s!"Expr.func.app.const :
e = {e}, e = {← ppExpr e}
fn = {fn}, fn = {← ppExpr fn}, fn.ctoName = {fn.ctorName}
arg = {arg}, arg = {← ppExpr arg}, arg.ctoName = {arg.ctorName}
c.ctorName = {c.ctorName}
"
-/
      match c with
      | Symbol _ (Basic (.ExprWithLimits .L_forall) _) =>
        return .Operator (.Special ⟨.anonymous⟩)
      | const .EmptyList =>
        return .const c
      | _ =>
        return .const nil

  | .lam ..  =>
    return .Operator (.ExprWithLimits .L_lambda)

  | .forallE ..  =>
    return .Operator (.ExprWithLimits .L_forall)

  | .letE ..    =>
    return .Operator (.ExprWithLimits .L_let)

  | .lit val =>
    match val with
    | .natVal val =>
      return .const (const (.natVal val))
    | .strVal val =>
      panic! s!"Expr.toExpr :
e = {e}, e.ctorName = {e.ctorName}, val = {val}"

  | .mdata _ e =>
    Expr.func e toExpr binders

  | .proj .. =>
    panic! s!"Expr.toExpr :
e = {e}, e.ctorName = {e.ctorName}"


def Expr.filter_default (func : Operator) (args : List Expr) : MetaM (List Expr) := do
  let name := func.name
  match name with
  | .anonymous =>
    return args
  | _ =>
    return List.zip (← func.name.binderInfo) args |>.filterMap fun (binderInfo, arg) =>
      match binderInfo with
      | .default => some arg
      | _ => none


def Expr.isProp : Expr → Bool
  | Basic func args =>
    match func, args with
    | .BinaryInfix op, _ => op.isProp
    | .UnaryPrefix op, _ => op.isProp
    | .ExprWithLimits .L_forall, expr :: _ => expr.isProp
    | .ExprWithAttr op, _ => op.isProp
    | .Special ⟨`ite⟩, [_, thenBranch, _] => thenBranch.isProp
    | _, _ => false
  | _ => false


def Binder.mk (binderinfo : BinderInfo) (binderType : Expr) : Binder :=
  match binderinfo with
  | .default => if binderType.isProp then .given else .default
  | .implicit => .implicit
  | .strictImplicit => .strictImplicit
  | .instImplicit => .instImplicit
