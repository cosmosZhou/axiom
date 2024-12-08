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
    from Axiom import Calculus, Algebra, Sets

    x, epsilon = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Equal(Limit[epsilon:-S.Infinitesimal]((f(x + epsilon) - f(x)) / epsilon), oo))

    Eq << Calculus.Eq_Limit.to.Any.All.limit_definition.apply(Eq[0], 'chi')

    Eq << Eq[-1].this.expr.apply(Algebra.All.to.All.And)

    Eq << Eq[-1].this.find(Element).apply(Sets.In_Interval.to.Lt)

    Eq << Eq[-1].this.expr.expr.apply(Algebra.Lt_0.Gt.to.Lt.Mul)

    Eq << Eq[-1].this.expr.expr.apply(Algebra.Lt.transport, lhs=0)


if __name__ == '__main__':
    run()
# created on 2020-04-27
