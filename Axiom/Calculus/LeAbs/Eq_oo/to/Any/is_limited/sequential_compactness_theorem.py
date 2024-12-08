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
    from Axiom import Sets, Algebra

    x = Symbol(real=True, shape=(oo,))
    n, m = Symbol(integer=True)
    # n is a sequence "peak" if x[m] <= x[n] foreach m > n
    Eq << apply(Sup[n:oo](Abs(x[n])) < oo, Equal(Card({n: All[m:n + 1:oo](x[m] <= x[n])}), oo))

    Eq << Sets.Eq_Card.to.Any.Eq.real.apply(Eq[1])

    i = Eq[-1].find(All[Less]).variable
    a = Eq[-1].variable
    # the sequence has infinitely many peaks, namely a0 < a1 < a2 < a3 < ... < a[j]
    Eq << Eq[-1].this.expr.apply(Sets.Eq_Cup.to.All)

    Eq << Algebra.Any.to.Any.And.limits.unleash.apply(Eq[-1])

    Eq << Eq[-1].this.find(All).apply(Algebra.All.limits.subs.offset, 1)

    Eq << Eq[-1].this.expr.apply(Algebra.All.All.to.All.And, simplify=None)

    # then the sequence x[a0] >= x[a1] >= x[a2] >= x[a3] > ... > x[a[j]] is a subsequence with the upper bound M
    Eq << Eq[-1].this.find(All).apply(Algebra.All.to.Or.subs, m, a[i + 1], ret=0, simplify=None)

    Eq << Eq[-1].this.find(Or).apply(Algebra.Or.to.All)

    Eq << Eq[-1].this.find(All[~And]).apply(Algebra.And.to.Cond, simplify=0)

    Eq << Eq[-1].this.find(Less).apply(Algebra.Lt.to.Le.strengthen, simplify=None)

    Eq << Eq[-1].this.find(Or).apply(Algebra.Or.to.And, simplify=None)

    Eq << Eq[-1].this.find(And).apply(Algebra.All.All.to.All.And, simplify=None)

    Eq << Eq[-1].this.find(All).apply(Algebra.All.to.All.subs.inner, m, a[i] + 1, simplify=None)

    Eq << Eq[-1].this.find(All).apply(Algebra.All_And.to.And.All, simplify=None)

    Eq << Eq[-1].this.find(All).limits_subs(i, n, simplify=None)

    Eq << Algebra.Any_And.to.Any.limits_absorb.apply(Eq[-1])

    Eq << Eq[-1].this.find(Less).apply(Algebra.Lt.to.Gt.reverse, simplify=None)

    Eq << Algebra.LtSup.to.Any.All.Lt.apply(Eq[0])

    M = Eq[-1].variable
    Eq << Any[M](All[n](Eq[-1].expr.expr), plausible=True)

    Eq << Eq[-1].this.expr.apply(Algebra.All.limits.domain_defined, simplify=None)


    Eq << Eq[-1].this.expr.apply(Algebra.All.to.Or.subs, n, a[i], simplify=None)
    return
    Eq << Eq[-1].this.expr.apply(Algebra.Cond.then.all, i)
    Eq << Eq[-1].this.expr.apply(Algebra.All.limits.domain_defined)
    #Eq << Eq[-1].this.find(Less[2]).apply(Algebra.Cond.then.Cond.domain_defined, ret=0)
    Eq << Eq[-1].this.expr.expr.apply(Algebra.Or.to.All, wrt=a[i], simplify=None)
    Eq << Eq[-1].this.expr.expr.apply(Algebra.All.limits.domain_defined, wrt=a[i], simplify=None)




if __name__ == '__main__':
    run()
# created on 2023-11-11
# updated on 2024-06-28
