from util import *


@apply
def apply(Any_All_et_ge):
    (((M, an1), (an1, an)), (n, S[0], S[oo])), (S[M],) = Any_All_et_ge.of(Any[All[LessEqual & LessEqual]])
    S[an1] = an._subs(n, n + 1)
    return Equal(Limit[n:oo](an), Inf[n:oo](an))


@prove
def prove(Eq):
    from Axiom import Algebra, Calculus

    a = Symbol(real=True, shape=(oo,), given=True)
    n = Symbol(integer=True)
    M = Symbol(real=True)
    Eq << apply(Exists[M](ForAll[n:oo]((M <= a[n + 1]) & (a[n + 1] <= a[n]))))

    Eq << Eq[0].this.find(And).apply(Algebra.Le.Le.to.Le.trans, ret=1)

    Eq << Eq[-1].this.expr.apply(Algebra.All_And.to.And.All)

    Eq << Algebra.And.to.And.apply(Eq[-1])

    Eq << Eq[-2].this.expr.expr.reversed

    Eq << Calculus.Le.Any_All_Ge.to.Limit.eq.Inf.monotone_convergence_theorem.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2024-06-27
