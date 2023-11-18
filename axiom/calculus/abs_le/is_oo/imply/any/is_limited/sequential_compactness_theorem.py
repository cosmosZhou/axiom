from util import *


@apply
def apply(given, is_oo, a=None):
    (x, n), M = given.of(Abs[Indexed] <= Expr)
    if a is None:
        a = given.generate_var(integer=True, shape=(oo,), var='a')

    S[n], (S[n], cond) = is_oo.of(Equal[Card[Cup[FiniteSet]], oo])
    ((S[x], m), S[x[n]]), (S[m], S[n + 1], S[oo]) = cond.of(All[Indexed <= Expr])

    return Any[a:All[n:1:oo](a[n - 1] < a[n])](Element(Limit[n:oo](x[a[n]]), Reals))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(real=True, shape=(oo,))
    M = Symbol(real=True, positive=True)
    n, m = Symbol(integer=True)
    Eq << apply(Abs(x[n]) <= M, Equal(Card({n: All[m:n + 1:oo](x[m] <= x[n])}), oo))

    Eq << sets.eq_card.imply.any.eq.real.apply(Eq[1])

    Eq << Eq[-1].this.expr.apply(sets.eq_cup.imply.all)

    Eq << algebra.any.imply.any.et.limits.unleash.apply(Eq[-1])

    Eq << Eq[-1].this.find(All).apply(algebra.all.limits.subs.offset, 1)

    Eq << Eq[-1].this.expr.apply(algebra.all.all.imply.all.et)
    


if __name__ == '__main__':
    run()
# created on 2023-11-11
# updated on 2023-11-18
