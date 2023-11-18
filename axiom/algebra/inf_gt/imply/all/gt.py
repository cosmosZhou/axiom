from util import *


@apply
def apply(le):
    (fx, *limits), M = le.of(Inf > Expr)
    return All(fx > M, *limits)


@prove
def prove(Eq):
    from axiom import algebra

    y, m, M, x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Inf[x:Interval(m, M, left_open=True, right_open=True)](f(x)) > y)

    z = Symbol(real=True)
    Eq << algebra.gt_inf.imply.any.all.gt.apply(Eq[0], z)

    Eq << algebra.any.imply.any.et.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.args[0].simplify()

    Eq << Eq[-1].this.expr.apply(algebra.cond.all.imply.all.et, simplify=None)

    Eq << Eq[-1].this.expr.expr.apply(algebra.gt.gt.imply.gt.transit)


if __name__ == '__main__':
    run()
# created on 2019-08-03
