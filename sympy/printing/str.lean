import sympy.core.expr
import std.String
import std.Level
open Lean (FVarId Name)


def Expr.strFormat : Expr → String
  | nil => ""

  | const _
  | sort _
  | Symbol .. =>
    "%s"

  | Basic func args =>
    let opStr := func.operator
    match func with
    | .BinaryInfix _ =>
      match args with
      | [left, right] =>
        let left :=
          if func.priority > left.priority then
            "(%s)"
          else
            "%s"
        let right :=
          if func.priority ≥ right.priority then
            "(%s)"
          else
            "%s"
        s!"{left} {opStr} {right}"

      | _ =>
        opStr

    | .UnaryPrefix _ =>
      let arg :=
        match args with
        | [arg] =>
          if func.priority > arg.priority then
            "(%s)"
          else
            "%s"
        | _ =>
          "%s"
      s!"{opStr}{arg}"

    | .UnaryPostfix _ =>
      match args with
      | [arg] =>
        let arg :=
          if func.priority > arg.priority then
            "(%s)"
          else
            "%s"
        s!"{arg}{opStr}"
      | _ =>
        s!"%s{opStr}"

    | .ExprWithLimits op =>
      match op, args with
      | .L_forall, [Symbol _ (sort u), _] =>
        match u with
        | .param _
        | .succ _ =>
          "%s → %s"
        | _ =>
          opStr ++ " %s".repeat (args.length - 1) ++ ", %s"
      | .L_lambda, _ =>
        opStr ++ " %s".repeat (args.length - 1) ++ " ↦ %s"
      | _, _ =>
        opStr ++ " %s".repeat (args.length - 1) ++ ", %s"

    | .Special op =>
      match op.name with
      | .anonymous =>
        let args := args.map fun arg =>
          if func.priority ≥ arg.priority then
            "(%s)"
          else
            "%s"
        " ".intercalate args
      | `ite =>
        "if %s then %s else %s"
      | `Prod.mk
      | `abs
      | `Norm.norm
      | `GetElem.getElem
      | _ =>
        opStr

    | .ExprWithAttr op =>
      match op with
      | .L_function _
      | .L_operatorname _ =>
        let args := args.map fun arg =>
          if func.priority ≥ arg.priority then
            "(%s)"
          else
            "%s"
        s!"{opStr} " ++ " ".intercalate args
      | .LMethod name =>
        let attr := name.getLast.toString
        match attr, args with
        | "map", [fn, obj] =>
          let fn :=
            if func.priority ≥ fn.priority then
              "(%s)"
            else
              "%s"
          let obj :=
            if func.priority ≥ obj.priority then
              "(%s)"
            else
              "%s"
          s!"{obj}.{attr} {fn}"
        | _, [obj, arg] =>
          let arg :=
            if func.priority > arg.priority then
              "(%s)"
            else
              "%s"
          let obj :=
            if func.priority ≥ obj.priority then
              "(%s)"
            else
              "%s"
          s!"{obj}.{attr} {arg}"
        | _, _ =>
          opStr
      | .L_typeclass _ =>
        opStr ++ " %s".repeat args.length
      | .LAttr _ =>
        match args with
        | [arg] =>
          let arg :=
            if func.priority > arg.priority then
              "(%s)"
            else
              "%s"
          s!"{arg}{opStr}"
        | _ =>
          s!"%s{opStr}"


  | Binder binder binderName _ value =>
    let binderName := " ".intercalate (binderName.components.map Name.toString)
    match binder with
    | .instImplicit =>
      binder.func.operator
    | .default =>
      if value == .nil then
        binder.func.operator.replaceFirst "%s" binderName
      else
        s!"({binderName} : %s := %s)"
    | _ =>
      binder.func.operator.replaceFirst "%s" binderName


partial def Expr.toString (e : Expr) : String :=
  e.strFormat.printf (strArgs e)
where
  strArgs : Expr → List String
  | nil => []

  | const val =>
    [val.toString]

  | sort u =>
    [u.toString]

  | Symbol name _ =>
    [name.normalized.toString]

  | Basic func args =>
    match func with
    | .ExprWithLimits op =>
      let args' :=
        match op with
        | .L_forall =>
          match args with
          | [returnType@(Symbol _ (sort u)), Binder .default _ binderType nil] =>
            match u with
            | .succ _
            | .param _ =>
              [binderType.toString, returnType.toString]
            | _ =>
              []
          | [returnType, Binder .given _ binderType@(Basic (.BinaryInfix ⟨`Membership.mem⟩) _) nil] =>
            [binderType.toString, returnType.toString]
          | _ =>
            []
        | .L_lambda =>
          match args with
          | expr :: limits =>
            let limits := limits.map fun arg =>
              match arg with
              | Binder .default name _ nil =>
                name.toString
              | _ =>
                arg.toString
            limits.reverse ++ [expr.toString]
          | .nil =>
            []
        | _ =>
          []
      if args' == [] then
        map args |>.reverse
      else
        args'
    | .Special ⟨`Nat.ModEq⟩ =>
      match args with
      | [d, a, b] =>
        [a.toString, b.toString, d.toString]
      | _ =>
        map args
    | .BinaryInfix ⟨`Membership.mem⟩
    | .ExprWithAttr (.LMethod (.str _ "map")) =>
      map args |>.reverse
    | _ =>
      map args

  | Binder (binderType := binderType) .. =>
    [binderType.toString]

  map : List Expr → List String
  | [] => []
  | head :: tail => head.toString :: map tail


instance : ToString Expr where
  toString := Expr.toString


instance : ToString Operator where
  toString : Operator → String
  | op => op.operator


instance : ToString FVarId where
  toString : FVarId → String
  | id => id.name.toString
