import sympy.core.expr
import std.String
import std.Level
import std.Name
open Lean (Name)


def Expr.countCases : Expr → Nat
  | Basic (.Special ⟨`ite⟩) args =>
    match args with
    | [_, _, elseBranch] =>
      elseBranch.countCases + 1
    | _ =>
      1
  | _ =>
    0


def Expr.latexFormat : Expr → String
  | nil => ""

  | const _
  | sort _
  | Symbol .. =>
    "%s"

  | e@(Basic func args) =>
    let opStr := func.command
    match func with
    | .BinaryInfix op =>
      match args with
      | [left, right] =>
        match op with
        | ⟨`HDiv.hDiv⟩
        | ⟨`Rat.divInt⟩ =>
          if let Basic (.BinaryInfix ⟨`HDiv.hDiv⟩) _ := left then
            "\\left. %s \\right/ %s"
          else
            s!"{opStr} %s %s"

        | ⟨`FloorDiv⟩ =>
          "%s {/\\!\\!/} %s"

        | ⟨`HPow.hPow⟩ =>
          let left :=
            match left with
            | Basic (.ExprWithAttr (.L_operatorname (.str _ "abs"))) _ =>
              "%s"
            | _ =>
              if func.priority > left.priority then
                "{\\left(%s\\right)}"
              else
                "%s"
          s!"{left} {opStr} %s"
        | _ =>
          let left :=
            if func.priority > left.priority then
              "{\\left(%s\\right)}"
            else
              "%s"
          let right :=
            if func.priority ≥ right.priority then
              if let Basic (.BinaryInfix ⟨`HDiv.hDiv⟩) _ := right then
                "%s"
              else
                "{\\left(%s\\right)}"
            else
              "%s"

          s!"{left} {opStr} {right}"

      | _ =>
        opStr

    | .UnaryPrefix _ =>
      if let [arg] := args then
        let arg :=
          if func.priority > arg.priority then
            "{\\left(%s\\right)}"
          else
            "%s"
        s!"{opStr}{arg}"
      else
        s!"{opStr}%s"

    | .UnaryPostfix op =>
      match op with
      | _ =>
        s!"%s{opStr}"

    | .ExprWithLimits op =>
      let opStr' :=
        match op with
        | .L_forall =>
          match args with
          | [Symbol _ (sort (.succ _)), _] =>
            "%s \\rightarrow %s"
          | [_, Binder .given _ type nil] =>
            match type with
            | Basic (.BinaryInfix ⟨`Membership.mem⟩) _ =>
              ""
            | _ =>
              "%s \\rightarrow %s"
          | _ =>
            ""
        | .L_lambda =>
          opStr ++ "\\ %s".repeat (args.length - 1) ++ "\\mapsto\\ %s"
        | .L_sum
        | .L_prod =>
          opStr ++ "\\limits_{\\substack{%s}} {%s}"
        | _ =>
          ""
      if opStr' == "" then
        opStr ++ "\\ %s".repeat (args.length - 1) ++ ",\\ %s"
      else
        opStr'

    | .Special op =>
      match op.name with
      | .anonymous =>
        let args := args.map fun arg =>
        if func.priority ≥ arg.priority then
          "{\\left(%s\\right)}"
        else
          "%s"
        "\\ ".intercalate args
      | `ite =>
        "\\begin{cases} %s \\\\ {%%s} & {\\color{blue}\\text{else}} \\end{cases}".format "\\\\".implode (List.replicate e.countCases "%s")
      | `Prod.mk
      | `abs
      | `Norm.norm
      | `GetElem.getElem
      | _ =>
        opStr
    | .ExprWithAttr op =>
      match op with
      | .L_function name =>
        let args := args.map fun arg =>
          if func.priority ≥ arg.priority then
            "\\left(%s\\right)"
          else
            "%s"
        opStr ++ "\\ " ++ "\\ ".intercalate args
      | .L_operatorname name =>
        match name with
        | `Complex.abs => "{\\left|%s\\right|}"
        | `Real.exp => "{\\color{RoyalBlue} e} ^ %s"
        | `Set.Ioo => "\\left(%s, %s\\right)"
        | `Set.Ico => "\\left[%s, %s\\right)"
        | `Set.Iio => "\\left(-\\infty, %s\\right]"
        | `Set.Icc => "\\left[%s, %s\\right]"
        | `Set.Iic => "\\left(-\\infty, %s\\right]"
        | `Set.Ioc => "\\left(%s, %s\\right]"
        | `Set.Ici => "\\left[%s, \\infty\\right)"
        | `Set.Ioi => "\\left(%s, \\infty\\right)"
        | _  =>
          let args := args.map fun arg =>
            if func.priority ≥ arg.priority then
              "\\left(%s\\right)"
            else
              "%s"
          opStr ++ "\\ " ++ "\\ ".intercalate args
      | .LMethod name =>
        let attr := name.getLast.toString
        match attr, args with
        | "map", [fn, obj] =>
          let fn :=
            if func.priority ≥ fn.priority then
              "\\left(%s\\right)"
            else
              "%s"
          let obj :=
            if func.priority ≥ obj.priority then
              "\\left(%s\\right)"
            else
              "%s"
          s!"{obj}.{attr}\\ {fn}"
        | "ediv", [left, right] =>
          let divOperator : BinaryInfix := ⟨`HDiv.hDiv⟩
          let func := divOperator.func
          let left :=
            if func.priority > left.priority then
              "{\\left(%s\\right)}"
            else
              "%s"
          let right :=
            if func.priority ≥ right.priority then
              "{\\left(%s\\right)}"
            else
              "%s"
          s!"{left} \\div {right}"
        | _, [obj, arg] =>
          let arg :=
            if func.priority > arg.priority then
              "\\left(%s\\right)"
            else
              "%s"
          let obj :=
            if func.priority ≥ obj.priority then
              "\\left(%s\\right)"
            else
              "%s"
          s!"{obj}.{attr}\\ {arg}"
        | _, _ =>
          opStr
      | .L_typeclass _ =>
        opStr ++ "\\ %s".repeat args.length
      | .LAttr name =>
        let attr := name.getLast.toString
        match name with
        | `Complex.exp =>
          "{\\color{RoyalBlue} e} ^ %s"
        | `Complex.cos
        | `Complex.sin
        | `Complex.log =>
          s!"\\{attr} %s"
        | `IsConstant.is_constant =>
          "%s\\ {\\color{blue}\\text{is}}\\ {constant}"
        | _ =>
          match args with
          | [arg] =>
            let arg :=
              if func.priority > arg.priority then
                "{\\left(%s\\right)}"
              else
                "%s"
            s!"{arg}.{attr}"
          | _ =>
            s!"%s.{attr}"

  | Binder binder binderName _ value =>
    let binderName := "\\ ".intercalate (binderName.components.map Name.toString)
    match binder with
    | .instImplicit =>
      binder.func.command
    | .default =>
      if value == .nil then
        binder.func.command.replaceFirst "%s" binderName
      else
        s!"\\left({binderName} : %s := %s\\right)"
    | _ =>
      binder.func.command.replaceFirst "%s" binderName


partial def Expr.toLatex (e : Expr) : String :=
  e.latexFormat.printf (latexArgs e)
where
  latexArgs : Expr → List String
  | nil => []

  | const val =>
    [val.toLatex]

  | sort u =>
    [u.toString]

  | Symbol name _ =>
    [name.normalized.toString.escape_underscore]

  | Basic func args =>
    match func with
    | .ExprWithLimits op =>
      let args' :=
        match op with
        | .L_forall =>
          match args with
          | [returnType@(Symbol _ (sort (.succ _))), Binder .default _ binderType nil]
          | [returnType, Binder .given _ binderType nil] =>
            [binderType.toLatex, returnType.toLatex]
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
                arg.toLatex
            limits.reverse ++ [expr.toLatex]
          | .nil =>
            []
        | .L_exists =>
          match args with
          | [expr, Binder .default name type nil] =>
            [("{%s : %s}".format name.toString, type.toLatex), expr.toLatex]
          | _ =>
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
        [a.toLatex, b.toLatex, d.toLatex]
      | _ =>
        map args
    | .BinaryInfix ⟨`Membership.mem⟩
    | .ExprWithAttr (.LMethod (.str _ "map")) =>
      map args |>.reverse
    | .Special ⟨`ite⟩ =>
      merge_ite e []
    | _ =>
      map args

  | Binder _ _ binderType value =>
    if value == nil then
      [binderType.toLatex]
    else
      [binderType.toLatex, value.toLatex]

  map : List Expr → List String
  | [] => []
  | head :: tail => ("{%s}".format head.toLatex) :: map tail

  merge_ite : Expr → List String → List String
  | Basic (.Special ⟨`ite⟩) args, cases =>
    match args with
    | [ifBranch, thenBranch, elseBranch] =>
      let cases := cases.concat ("{{%s}} & {\\color{blue}\\text{if}}\\ %s ".format thenBranch.toLatex, ifBranch.toLatex)
      merge_ite elseBranch cases
    | _=>
      cases
  | e, cases =>
    cases.concat e.toLatex


def Expr.latex_tagged (expr : Expr) (hypId : Name) (color : String := "green") : String :=
  "%s\\tag*{$\\color{%s}%s$}".format expr.toLatex, color, ".".intercalate (
    hypId.normalized.components.map (·.toString.escape_underscore)
  )
