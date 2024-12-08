from util import *


@apply
def apply(lamda):
    expr, (i, S[0], n), (j, S[0], S[n]) = lamda.of(Lamda)
    S[i], expr = expr.of(KroneckerDelta[j] * Expr)

    if expr._has(j):
        assert not expr._has(i)
        return Equal(lamda, Identity(n) * Lamda[j:n](expr).simplify())
    elif expr._has(i):
        assert not expr._has(j)
        return Equal(lamda, Identity(n) * Lamda[i:n](expr).simplify())


@prove
def prove(Eq):
    from Axiom import Algebra

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    a = Symbol(real=True, shape=(oo,))
    Eq << apply(Lamda[j:n, i:n](a[j] * KroneckerDelta(i, j)))

    i = Symbol(domain=Range(n))
    Eq << Algebra.Eq.of.Eq.getitem.apply(Eq[0], i)




if __name__ == '__main__':
    run()

# created on 2019-10-17
# updated on 2021-12-30