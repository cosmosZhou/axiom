from util import *


@apply
def apply(eq_limit):
    tangent, (epsilon, S[-S.Infinitesimal]) = eq_limit.of(Equal[Limit, Infinity])
    delta = tangent * epsilon
    fx1, fx = delta.of(Expr - Expr)
    for x in fx.free_symbols:
        if fx1 == fx._subs(x, x + epsilon):
            break
    else:
        raise

    return Limit[epsilon:-S.Infinitesimal](fx1) < fx


@prove(proved=False)
def prove(Eq):
    from axiom import calculus, algebra, sets

    x, epsilon = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Equal(Limit[epsilon:-S.Infinitesimal]((f(x + epsilon) - f(x)) / epsilon), oo))

    Eq << calculus.eq_limit.imply.any.all.limit_definition.apply(Eq[0], 'chi')

    Eq << Eq[-1].this.expr.apply(algebra.all.imply.all.et)

    Eq << Eq[-1].this.find(Element).apply(sets.el_interval.imply.lt)

    Eq << Eq[-1].this.expr.expr.apply(algebra.lt_zero.gt.imply.lt.mul)

    Eq << Eq[-1].this.expr.expr.apply(algebra.lt.transport, lhs=0)


if __name__ == '__main__':
    run()
# created on 2020-04-27
