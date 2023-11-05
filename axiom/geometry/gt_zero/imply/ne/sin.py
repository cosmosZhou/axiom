from util import *


@apply
def apply(gt_zero):
    x = gt_zero.of(Expr > 0)
    return Unequal(sin(x), x)


@prove
def prove(Eq):
    from axiom import algebra, calculus, sets, geometry

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

    Eq.eq = algebra.eq.eq.imply.eq.transit.apply(Eq.f0, Eq[-1])

    Eq.lt = Eq[0].reversed

    Eq.all_eq = All[ξ : Interval(0, x)](Equal(Limit[t:ξ](f(t)), f(ξ)), plausible=True)

    Eq << Eq.all_eq.subs(Eq.fxi, Eq.ft)

    Eq << Eq[-1].this.find(Limit).doit()

    Eq.all_el = All[t:0:x](Element(Derivative[t](f(t)), Interval(-oo, oo)), plausible=True)

    
    Eq << Eq.all_el.subs(Eq.ft)

    Eq << Eq[-1].this.find(Derivative).apply(calculus.grad.to.add)

    Eq << calculus.lt.is_continuous.is_differentiable.eq.imply.any_eq.Rolle.apply(Eq.lt, Eq.all_eq, Eq.all_el, Eq.eq)

    Eq << Eq[-1].subs(Eq.ft)

    Eq << Eq[-1].this.find(Derivative).apply(calculus.grad.to.add)

    Eq << algebra.any.imply.any_et.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).apply(sets.el_interval.imply.et)

    Eq << geometry.imply.el.sin.apply(x)

    Eq << algebra.cond.any.imply.any.et.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].subs(Eq[2])

    Eq << Eq[-1].this.find(Element).apply(sets.el_interval.imply.le)

    Eq << Eq[-1].this.expr.args[1::2].apply(algebra.lt.le.imply.lt.transit)

    Eq << Eq[-1].this.expr.args[1:].apply(sets.lt.gt.imply.el.interval, simplify=None)

    Eq << Eq[-1].this.find(Element).apply(geometry.el_interval.imply.gt_zero.sin)

    Eq << Eq[-1].this.find(Equal).reversed

    Eq << geometry.imply.eq.add.square.apply(t)

    Eq << algebra.cond.any.imply.any.et.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.expr.args[:2].apply(algebra.eq.eq.imply.eq.subs, swap=True)

    Eq << Eq[-1].this.find(Expr > 0).apply(algebra.gt_zero.imply.gt_zero.square)

    #updated on 2023-10-03


# updated on 2023-10-03
