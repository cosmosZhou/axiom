from util import *


@apply
def apply(given):
    x, S = given.of(Element)
    return GreaterEqual(Card(S), 1)


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    n = Symbol(integer=True, positive=True, given=True)
    x = Symbol(complex=True, shape=(n,), given=True)
    S = Symbol(etype=dtype.complex[n], given=True)
    Eq << apply(Element(x, S))

    Eq << Set.Ne_EmptySet.of.Mem.apply(Eq[0])

    Eq << Set.Gt_0.of.Ne_EmptySet.apply(Eq[-1])

    Eq << Algebra.Ge.of.Gt.strengthen.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-03-10
