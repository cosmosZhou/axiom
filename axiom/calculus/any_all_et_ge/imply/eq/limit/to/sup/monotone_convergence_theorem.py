from util import *


@apply
def apply(any_all_et_ge):
    (((M, an1), (an1, an)), (n, S[0], S[oo])), (S[M],) = any_all_et_ge.of(Any[All[GreaterEqual & GreaterEqual]])
    S[an1] = an._subs(n, n + 1)
    return Equal(Limit[n:oo](an), Sup[n:oo](an))


@prove
def prove(Eq):
    from axiom import algebra, calculus
    
    a = Symbol(real=True, shape=(oo,), given=True)
    n = Symbol(integer=True)
    M = Symbol(real=True)
    Eq << apply(Exists[M](ForAll[n:oo]((M >= a[n + 1]) & (a[n + 1] >= a[n]))))
    
    Eq << Eq[0].this.find(And).apply(algebra.ge.ge.imply.ge.transit, ret=1)
    
    Eq << Eq[-1].this.expr.apply(algebra.all_et.imply.et.all)
    
    Eq << algebra.et.imply.et.apply(Eq[-1])
    
    Eq << Eq[-2].this.expr.expr.reversed
    
    Eq << calculus.ge.any_all_le.imply.eq.limit.to.sup.monotone_convergence_theorem.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2024-06-27
