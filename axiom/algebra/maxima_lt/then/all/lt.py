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

    Eq << algebra.lt.then.le.relax.apply(Eq[0])

    Eq << algebra.maxima_le.then.all.le.apply(Eq[-1])

    Eq << algebra.cond.of.et.infer.split.apply(Eq[1], cond=Equal(S, S.etype.emptySet))

    Eq << algebra.infer.of.infer.subs.apply(Eq[-2])

    Eq << Eq[-1].this.rhs.expr.apply(algebra.lt.of.et)

    Eq << Eq[-1].this.rhs.apply(algebra.all_et.of.et.all)

    Eq << algebra.infer.of.et.infer.apply(Eq[-1])

    Eq << algebra.infer.of.cond.apply(Eq[-1])

    Eq.infer_is_empty = Eq[-2].this.apply(algebra.infer.contraposition)

    Eq << Eq[0].this.lhs.limits_subs(x, t)

    Eq << algebra.then.all.le_maxima.apply(Eq[0].lhs)

    Eq << Eq[-1].limits_subs(t, x)

    Eq << algebra.cond.infer.of.et.infer.et.apply(Eq[-1], Eq.infer_is_empty)

    Eq << Eq[-1].this.lhs.apply(algebra.all.any.then.any.et)

    Eq << Eq[-1].this.lhs.expr.apply(algebra.eq.le.then.le.trans)

    Eq << algebra.cond.infer.of.et.infer.et.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-11-12
