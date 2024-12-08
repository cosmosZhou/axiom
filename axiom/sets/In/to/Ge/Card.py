from util import *


@apply
def apply(given):
    x, S = given.of(Element)
    return GreaterEqual(Card(S), 1)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    n = Symbol(integer=True, positive=True, given=True)
    x = Symbol(complex=True, shape=(n,), given=True)
    S = Symbol(etype=dtype.complex[n], given=True)
    Eq << apply(Element(x, S))

    Eq << Sets.In.to.Ne_EmptySet.apply(Eq[0])

    Eq << Sets.Ne_EmptySet.to.Gt_0.apply(Eq[-1])

    Eq << Algebra.Gt.to.Ge.strengthen.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-03-10
