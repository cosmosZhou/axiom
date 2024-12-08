from util import *


@apply
def apply(le):
    (fx, *limits), M = le.of(Sup < Expr)
    return All(fx < M, *limits)


@prove
def prove(Eq):
    from Axiom import Algebra

    y, m, M, x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Sup[x:Interval(m, M, left_open=True, right_open=True)](f(x)) < y)

    z = Symbol(real=True)
    Eq << Algebra.LtSup.to.Any.All.Lt.apply(Eq[0], z)

    Eq << Algebra.Any.to.Any.And.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.args[0].simplify()

    Eq << Eq[-1].this.expr.apply(Algebra.Cond.All.to.All.And, simplify=None)
    Eq << Eq[-1].this.expr.expr.apply(Algebra.Lt.Lt.to.Lt.trans)


if __name__ == '__main__':
    run()
# created on 2020-01-15
