from util import *




@apply
def apply(given, S):
    lhs, rhs = given.of(Supset)
    return Supset(lhs, rhs & S)


@prove
def prove(Eq):
    from Axiom import Sets
    n = Symbol(integer=True, positive=True)
    A, B, S = Symbol(etype=dtype.complex[n])

    Eq << apply(Supset(A, B), S)

    Eq << Eq[0].reversed

    Eq << Sets.Subset.to.Subset.restrict.apply(Eq[-1], S)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2021-07-05