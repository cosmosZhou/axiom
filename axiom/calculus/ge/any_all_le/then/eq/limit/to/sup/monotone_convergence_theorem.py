from util import *


@apply
def apply(ge, any_all_le):
    ((an, M), (n, S[0], S[oo])), (S[M],) = any_all_le.of(Any[All[LessEqual]])
    S[an._subs(n, n + 1)], S[an] = ge.of(GreaterEqual)
    return Equal(Limit[n:oo](an), Sup[n:oo](an))


@prove
def prove(Eq):
    from axiom import algebra, sets, calculus

    a = Symbol(real=True, shape=(oo,), given=True)
    n = Symbol(integer=True)
    M = Symbol(real=True)
    Eq << apply(a[n + 1] >= a[n], Exists[M](ForAll[n:oo](a[n] <= M)))

    N = Symbol(integer=True, nonnegative=True)
    epsilon = Symbol(real=True, positive=True)
    Eq.any_gt = Exists[N](a[N] > Eq[2].find(Sup) - epsilon, plausible=True)

    Eq << ~Eq.any_gt

    Eq << Eq[-1].this.expr.apply(algebra.all_le.then.sup_le)

    Eq.any_le = Eq[-1].this.find(Sup).limits_subs(N, n)

    Eq << Eq[1].this.expr.apply(algebra.all_le.then.sup_le)

    Eq << Eq[-1].this.expr.apply(algebra.le.then.lt.relax, upper=oo)

    Eq.ge_sup = algebra.then.all.sup_ge.apply(Eq[-1].lhs)

    Eq << algebra.ge.then.gt.relax.apply(Eq.ge_sup, lower=-oo)

    Eq.sup_is_real = sets.lt.gt.then.el.interval.apply(Eq[-2], Eq[-1], simplify=None)

    Eq << algebra.cond.any.then.any.et.apply(Eq.sup_is_real, Eq.any_le, simplify=None)

    Eq << Eq[-1].this.expr.apply(sets.le.el.then.le.sub)

    Eq << Eq.any_gt.this.expr + epsilon

    Eq << Eq[-1].this.expr.reversed

    Eq.any_lt = Eq[-1].this.expr - a[N]

    Eq << algebra.ge.then.all.ge.monotone.apply(Eq[0], n, N)

    Eq << algebra.all.then.all.limits.restrict.apply(Eq[-1], domain=Range(N + 1, oo))

    Eq << -Eq[-1].this.expr

    Eq << algebra.cond.all.then.all.et.apply(Eq.sup_is_real, Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(sets.le.el.then.le.add)

    Eq << algebra.all.any.then.any.all.et.apply(Eq[-1], Eq.any_lt)

    Eq << Eq[-1].this.expr.expr.apply(algebra.lt.le.then.lt.trans)

    Eq << algebra.ge.then.eq.abs.apply(Eq.ge_sup)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.find(Abs).apply(algebra.abs.neg)

    Eq << calculus.any_all.then.eq.limit_definition.apply(Eq[-1])

    # https://en.wikipedia.org/wiki/Least-upper-bound_property
    # https://en.wikipedia.org/wiki/Monotone_convergence_theorem




if __name__ == '__main__':
    run()
# created on 2020-05-20
# updated on 2023-11-11
