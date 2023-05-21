from util import *


@apply
def apply(lamda):
    delta, (i, S[0], n), (j, S[0], S[n]) = lamda.of(Lamda)

    S[i] = delta.of(KroneckerDelta[j])
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
# created on 2023-03-18
