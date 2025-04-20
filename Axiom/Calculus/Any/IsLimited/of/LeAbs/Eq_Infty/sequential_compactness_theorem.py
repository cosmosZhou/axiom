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
    from Axiom import Set, Algebra, Logic

    x = Symbol(real=True, shape=(oo,))
    n, m = Symbol(integer=True)
    # n is a sequence "peak" if x[m] <= x[n] foreach m > n
    Eq << apply(Sup[n:oo](Abs(x[n])) < oo, Equal(Card({n: All[m:n + 1:oo](x[m] <= x[n])}), oo))

    Eq << Set.Any.Eq.of.Eq_Card.real.apply(Eq[1])

    i = Eq[-1].find(All[Less]).variable
    a = Eq[-1].variable
    # the sequence has infinitely many peaks, namely a0 < a1 < a2 < a3 < ... < a[j]
    Eq << Eq[-1].this.expr.apply(Set.All.of.Eq_Cup)

    Eq << Algebra.Any.And.of.Any.limits.unleash.apply(Eq[-1])

    Eq << Eq[-1].this.find(All).apply(Algebra.All.limits.subs.offset, 1)

    Eq << Eq[-1].this.expr.apply(Algebra.All.And.of.All.All, simplify=None)

    # then the sequence x[a0] >= x[a1] >= x[a2] >= x[a3] > ... > x[a[j]] is a subsequence with the upper bound M
    Eq << Eq[-1].this.find(All).apply(Algebra.Or.of.All.subs, m, a[i + 1], ret=0, simplify=None)

    Eq << Eq[-1].this.find(Or).apply(Algebra.All.of.Or)

    Eq << Eq[-1].this.find(All[~And]).apply(Logic.Cond.of.And, simplify=0)

    Eq << Eq[-1].this.find(Less).apply(Algebra.Le.of.Lt.strengthen, simplify=None)

    Eq << Eq[-1].this.find(Or).apply(Algebra.And.of.Or, simplify=None)

    Eq << Eq[-1].this.find(And).apply(Algebra.All.And.of.All.All, simplify=None)

    Eq << Eq[-1].this.find(All).apply(Algebra.All.of.All.subs.inner, m, a[i] + 1, simplify=None)

    Eq << Eq[-1].this.find(All).apply(Algebra.And.All.of.All_And, simplify=None)

    Eq << Eq[-1].this.find(All).limits_subs(i, n, simplify=None)

    Eq << Algebra.Any.of.Any_And.limits_absorb.apply(Eq[-1])

    Eq << Eq[-1].this.find(Less).apply(Algebra.Gt.of.Lt.reverse, simplify=None)

    Eq << Algebra.Any.All.Lt.of.LtSup.apply(Eq[0])

    M = Eq[-1].variable
    Eq << Any[M](All[n](Eq[-1].expr.expr), plausible=True)

    Eq << Eq[-1].this.expr.apply(Algebra.All.limits.domain_defined, simplify=None)


    Eq << Eq[-1].this.expr.apply(Algebra.Or.of.All.subs, n, a[i], simplify=None)
    return
    Eq << Eq[-1].this.expr.apply(Algebra.Cond.then.all, i)
    Eq << Eq[-1].this.expr.apply(Algebra.All.limits.domain_defined)
    #Eq << Eq[-1].this.find(Less[2]).apply(Algebra.Cond.then.Cond.domain_defined, ret=0)
    Eq << Eq[-1].this.expr.expr.apply(Algebra.All.of.Or, wrt=a[i], simplify=None)
    Eq << Eq[-1].this.expr.expr.apply(Algebra.All.limits.domain_defined, wrt=a[i], simplify=None)




if __name__ == '__main__':
    run()
# created on 2023-11-11
# updated on 2024-06-28
