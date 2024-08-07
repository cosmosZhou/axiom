from util import *


@apply
def apply(eq, sgm):
    X, n = eq.of(Equal[Card])
    fx, (x, S[X]) = sgm.of(Sum)
    (a, i), (S[i], S[0], S[n]) = X.of(Cup[FiniteSet[Indexed]])
    if fx._has(i):
        i = sgm.generate_var({i}, integer=True)
    return Equal(sgm, Sum[i:n](fx._subs(x, a[i])))


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True)
    a = Symbol(real=True, shape=(oo,))
    f = Function(real=True)
    s = a[:n].cup_finiteset()
    Eq << apply(Equal(Card(s), n), Sum[x:s](f(x)))

    Eq << sets.eq.imply.all.ne.apply(Eq[0])

    Eq << algebra.all_ne.imply.eq.sum.double_limits.apply(Eq[-1], Eq[1].lhs)





if __name__ == '__main__':
    run()
# created on 2021-03-20
# updated on 2023-05-21
