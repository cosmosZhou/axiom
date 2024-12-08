from util import *


@apply
def apply(given, S):
    lhs, rhs = given.of(Subset)
    return Subset(lhs - S, rhs)

@prove
def prove(Eq):
    from Axiom import Sets

    n = Symbol(integer=True, positive=True)
    A, B, S = Symbol(etype=dtype.complex[n])
    Eq << apply(Subset(A, B), S)

    Eq << Subset(A - S, A, plausible=True)
    Eq << Sets.Subset.Subset.to.Subset.trans.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2021-06-27
