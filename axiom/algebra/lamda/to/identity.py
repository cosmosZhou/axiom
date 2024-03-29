from util import *


@apply
def apply(lamda):
    (_i, _j), (i, n), (j, S[n]) = lamda.of(Lamda[KroneckerDelta, Tuple[0, Expr], Tuple[0, Expr]])

    assert {i, j} == {_i, _j}

    return Equal(lamda, Identity(n))


@prove
def prove(Eq):
    from axiom import algebra
    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)

    Eq << apply(Lamda[j:n, i:n](KroneckerDelta(i, j)))

    i = Symbol(domain=Range(n))

    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)


if __name__ == '__main__':
    run()

# created on 2018-04-16
