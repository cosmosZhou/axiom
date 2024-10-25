from util import *


@apply
def apply(sup_lt_oo, is_oo, a=None):
    (x, n), (S[n], S[0], S[oo]) = sup_lt_oo.of(Sup[Abs[Indexed]] < Infinity)
    if a is None:
        a = sup_lt_oo.generate_var(integer=True, shape=(oo,), var='a')

    S[n], (S[n], cond) = is_oo.of(Equal[Card[Cup[FiniteSet]], oo])
    ((S[x], m), S[x[n]]), (S[m], S[n + 1], S[oo]) = cond.of(All[Indexed <= Expr])

    return Any[a:All[n:oo](a[n + 1] > a[n])](Element(Limit[n:oo](x[a[n]]), Reals))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(real=True, shape=(oo,))
    n, m = Symbol(integer=True)
    # n is a sequence "peak" if x[m] <= x[n] foreach m > n
    Eq << apply(Sup[n:oo](Abs(x[n])) < oo, Equal(Card({n: All[m:n + 1:oo](x[m] <= x[n])}), oo))

    Eq << sets.eq_card.then.any.eq.real.apply(Eq[1])

    i = Eq[-1].find(All[Less]).variable
    a = Eq[-1].variable
    # the sequence has infinitely many peaks, namely a0 < a1 < a2 < a3 < ... < a[j]
    Eq << Eq[-1].this.expr.apply(sets.eq_cup.then.all)

    Eq << algebra.any.then.any.et.limits.unleash.apply(Eq[-1])

    Eq << Eq[-1].this.find(All).apply(algebra.all.limits.subs.offset, 1)

    Eq << Eq[-1].this.expr.apply(algebra.all.all.then.all.et, simplify=None)

    # then the sequence x[a0] >= x[a1] >= x[a2] >= x[a3] > ... > x[a[j]] is a subsequence with the upper bound M
    Eq << Eq[-1].this.find(All).apply(algebra.all.then.ou.subs, m, a[i + 1], ret=0, simplify=None)

    Eq << Eq[-1].this.find(Or).apply(algebra.ou.then.all)

    Eq << Eq[-1].this.find(All[~And]).apply(algebra.et.then.cond, simplify=0)

    Eq << Eq[-1].this.find(Less).apply(algebra.lt.then.le.strengthen, simplify=None)

    Eq << Eq[-1].this.find(Or).apply(algebra.ou.then.et, simplify=None)

    Eq << Eq[-1].this.find(And).apply(algebra.all.all.then.all.et, simplify=None)

    Eq << Eq[-1].this.find(All).apply(algebra.all.then.all.subs.inner, m, a[i] + 1, simplify=None)

    Eq << Eq[-1].this.find(All).apply(algebra.all_et.then.et.all, simplify=None)

    Eq << Eq[-1].this.find(All).limits_subs(i, n, simplify=None)

    Eq << algebra.any_et.then.any.limits_absorb.apply(Eq[-1])

    Eq << Eq[-1].this.find(Less).apply(algebra.lt.then.gt.reverse, simplify=None)

    Eq << algebra.sup_lt.then.any.all.lt.apply(Eq[0])

    M = Eq[-1].variable
    Eq << Any[M](All[n](Eq[-1].expr.expr), plausible=True)

    Eq << Eq[-1].this.expr.apply(algebra.all.limits.domain_defined, simplify=None)


    Eq << Eq[-1].this.expr.apply(algebra.all.then.ou.subs, n, a[i], simplify=None)
    return
    Eq << Eq[-1].this.expr.apply(algebra.cond.then.all, i)
    Eq << Eq[-1].this.expr.apply(algebra.all.limits.domain_defined)
    #Eq << Eq[-1].this.find(Less[2]).apply(algebra.cond.then.cond.domain_defined, ret=0)
    Eq << Eq[-1].this.expr.expr.apply(algebra.ou.then.all, wrt=a[i], simplify=None)
    Eq << Eq[-1].this.expr.expr.apply(algebra.all.limits.domain_defined, wrt=a[i], simplify=None)




if __name__ == '__main__':
    run()
# created on 2023-11-11
# updated on 2024-06-28
