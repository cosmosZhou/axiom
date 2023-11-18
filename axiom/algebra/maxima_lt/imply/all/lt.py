from util import *


@apply
def apply(given):
    (fx, *limits), M = given.of(Less[Maxima])
    return All(fx < M, *limits)


@prove
def prove(Eq):
    from axiom import algebra

    x, t = Symbol(real=True)
    M = Symbol(real=True, given=True)
    f = Function(real=True)
    S = Symbol(etype=dtype.real)
    Eq << apply(Maxima[x:S](f(x)) < M)

    Eq << algebra.lt.imply.le.relax.apply(Eq[0])

    Eq << algebra.maxima_le.imply.all.le.apply(Eq[-1])

    Eq << algebra.cond.given.et.infer.split.apply(Eq[1], cond=Equal(S, S.etype.emptySet))

    Eq << algebra.infer.given.infer.subs.apply(Eq[-2])

    Eq << Eq[-1].this.rhs.expr.apply(algebra.lt.given.et)

    Eq << Eq[-1].this.rhs.apply(algebra.all_et.given.et.all)

    Eq << algebra.infer.given.et.infer.apply(Eq[-1])

    Eq << algebra.infer.given.cond.apply(Eq[-1])

    Eq.infer_is_empty = Eq[-2].this.apply(algebra.infer.contraposition)

    Eq << Eq[0].this.lhs.limits_subs(x, t)

    Eq << algebra.imply.all.le_maxima.apply(Eq[0].lhs)

    Eq << Eq[-1].limits_subs(t, x)

    Eq << algebra.cond.infer.given.et.infer.et.apply(Eq[-1], Eq.infer_is_empty)

    Eq << Eq[-1].this.lhs.apply(algebra.all.any.imply.any.et)

    Eq << Eq[-1].this.lhs.expr.apply(algebra.eq.le.imply.le.transit)

    Eq << algebra.cond.infer.given.et.infer.et.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-11-12
