from util import *


@apply
def apply(given, S):
    lhs, rhs = given.of(Subset)
    return Subset(lhs | S, rhs | S)

@prove
def prove(Eq):
    from Axiom import Sets
    n = Symbol(integer=True, positive=True)
    A, B, S = Symbol(etype=dtype.complex[n])

    Eq << apply(Subset(A, B), S)

    Eq << Sets.Subset.to.Subset.Union.rhs.apply(Eq[0], S)

    Eq << Subset(S, B | S, plausible=True)

    Eq <<= Eq[-1] & Eq[-2]

if __name__ == '__main__':
    run()


# created on 2020-07-19
from . import rhs