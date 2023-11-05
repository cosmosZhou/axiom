from util import *


@apply
def apply(is_limited):
    from axiom.calculus.is_limited.imply.any.all.limit_definition import of_limited
    fx, (x, x0) = of_limited(is_limited, nonzero=True)

    return Equal(Limit[x:x0](1 / fx), 1 / is_limited.lhs)


@prove
def prove(Eq):
    from axiom import calculus, sets, algebra

    x, x0 = Symbol(real=True)
    g = Function(real=True)
    Eq << apply(Element(Limit[x:x0](g(x)), Reals - {0}))

    ε_0 = Symbol(real=True, positive=True)
    δ_0 = Symbol(real=True, positive=True)
    Eq << calculus.is_limited.imply.any.all.limit_definition.symbol_subs.apply(Eq[0], ε_0, δ_0, var='A')

    A = Eq[-1].find(Abs[Add[-~Symbol]])
    Eq.is_limited = A.this.definition.reversed

    Eq.is_nonzero_real = Eq[0].subs(Eq.is_limited)

    Eq << sets.el.imply.ne_zero.apply(Eq.is_nonzero_real)

    Eq << algebra.ne_zero.eq.imply.eq.inverse.apply(Eq[-1], Eq.is_limited)

    Eq << Eq[1].subs(Eq[-1])

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.is_limited)

    δ_1 = Symbol(positive=True)
    Eq << calculus.eq_limit.el.imply.any.all.lt.half.apply(Eq.is_limited, Eq.is_nonzero_real, delta=δ_1)

    Eq.A_is_positive = sets.is_nonzero.imply.gt_zero.abs.apply(Eq.is_nonzero_real)

    Eq << algebra.cond.any_all.imply.any.all.et.apply(Eq.A_is_positive / 2, Eq[-1])

    Eq << Eq[-1].this.expr.expr.apply(algebra.gt_zero.gt.imply.lt.inverse)

    Eq << algebra.gt_zero.imply.gt_zero.div.apply(Eq.A_is_positive)

    Eq << algebra.cond.any_all.imply.any.all.et.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.expr.expr.apply(algebra.gt_zero.lt.imply.lt.mul)


    Eq << algebra.any_all.any_all.imply.any.all.et.limits_intersect.apply(Eq[2], Eq[-1])
    Eq << Eq[-1].this.expr.expr.apply(algebra.lt.lt.imply.lt.mul)
    Eq << Eq[-1].this.find(Mul[Abs]).apply(algebra.mul.to.abs)
    Eq << Eq[-1].this.find(Abs[~Mul]).apply(algebra.mul.to.add)
    Eq << Eq[-1].this.expr.expr.lhs.apply(algebra.abs.neg)
    Eq << Eq[-1].this.expr.limits[0][1].args[0].apply(sets.lt.given.el.interval)
    Eq << Eq[-1].this.expr.limits[0][1].args[0].apply(sets.lt.given.el.interval)
    Eq << Eq[-1].this.expr.limits[0][1].args[1].simplify()
    ε, δ = Symbol(positive=True)
    Eq << algebra.cond.imply.ou.subs.apply(Eq[-1], ε_0, abs(A) ** 2 / 2 * ε)
    Eq << algebra.gt_zero.imply.gt_zero.square.apply(Eq.A_is_positive) * ε / 2
    Eq << algebra.cond.ou.imply.cond.apply(Eq[-1], Eq[-2])
    Eq << algebra.any.imply.any.subs.apply(Eq[-1], Min(δ_0, δ_1), δ)
    Eq << calculus.any_all.imply.eq.limit_definition.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2020-06-18
# updated on 2023-04-16
