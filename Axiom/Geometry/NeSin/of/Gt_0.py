from util import *


@apply
def apply(gt_zero):
    x = gt_zero.of(Expr > 0)
    return Unequal(sin(x), x)


@prove
def prove(Eq):
    from Axiom import Algebra, Calculus, Set, Geometry

    x = Symbol(real=True, given=True)
    Eq << apply(x > 0)

    Eq << ~Eq[1]

    @Function(real=True)
    def f(t):
        return sin(t) - t
    t, ξ = Symbol(real=True)
    Eq.ft = f(t).this.defun()

    Eq.fxi, Eq.f0, Eq.fx = Eq.ft.subs(t, ξ), Eq.ft.subs(t, 0), Eq.ft.subs(t, x)

    Eq << Eq.fx.subs(Eq[2])

    Eq.eq = Algebra.Eq.of.Eq.Eq.apply(Eq.f0, Eq[-1])

    Eq.lt = Eq[0].reversed

    Eq.All_Eq = All[ξ : Interval(0, x)](Equal(Limit[t:ξ](f(t)), f(ξ)), plausible=True)

    Eq << Eq.All_Eq.subs(Eq.fxi, Eq.ft)

    Eq << Eq[-1].this.find(Limit).doit()

    Eq.all_el = All[t:0:x](Element(Derivative[t](f(t)), Interval(-oo, oo)), plausible=True)


    Eq << Eq.all_el.subs(Eq.ft)

    Eq << Eq[-1].this.find(Derivative).apply(Calculus.Grad.eq.Add)

    Eq << Calculus.Any.Eq.Rolle.of.Lt.IsContinuous.IsDifferentiable.Eq.apply(Eq.lt, Eq.All_Eq, Eq.all_el, Eq.eq)

    Eq << Eq[-1].subs(Eq.ft)

    Eq << Eq[-1].this.find(Derivative).apply(Calculus.Grad.eq.Add)

    Eq << Algebra.Any.And.of.Any.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).apply(Set.And.of.Mem_Icc)

    Eq << Geometry.Sin.In.Icc.apply(x)

    Eq << Algebra.Any.And.of.Cond.Any.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].subs(Eq[2])

    Eq << Eq[-1].this.find(Element).apply(Set.Le.of.Mem_Icc)

    Eq << Eq[-1].this.expr.args[1::2].apply(Algebra.Lt.of.Lt.Le)

    Eq << Eq[-1].this.expr.args[1:].apply(Set.Mem.Icc.of.Lt.Gt, simplify=None)

    Eq << Eq[-1].this.find(Element).apply(Geometry.Gt_0.Sin.of.Mem_Icc)

    Eq << Eq[-1].this.find(Equal).reversed

    Eq << Geometry.Add_.SquareCos.SquareSin.eq.One.apply(t)

    Eq << Algebra.Any.And.of.Cond.Any.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.expr.args[:2].apply(Algebra.Eq.of.Eq.Eq.subs, swap=True)

    Eq << Eq[-1].this.find(Expr > 0).apply(Algebra.Gt_0.Square.of.Gt_0)

    # updated on 2023-10-03


# updated on 2023-10-03
