from util import *


@apply
def apply(le):
    (fx, *limits), M = le.of(Sup <= Expr)
    return All(fx <= M, *limits)


@prove
def prove(Eq):
    from Axiom import Algebra

    m, M, x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Sup[x:Interval(m, M, left_open=True, right_open=True)](f(x)) <= M)

    Eq << Eq[0].this.lhs.apply(Algebra.Sup.eq.ReducedMin)

    Eq << Eq[-1].this.lhs.apply(Algebra.ReducedMin.eq.Minima)

    Eq << Algebra.LeMinima.to.Any.Le.apply(Eq[-1])

    Eq << Algebra.Any.to.Any.And.limits.unleash.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(Algebra.Cond.All.to.All.And, simplify=None)

    Eq << Eq[-1].this.expr.expr.apply(Algebra.Le.Le.to.Le.trans)


if __name__ == '__main__':
    run()
# created on 2018-12-27
# updated on 2021-09-30