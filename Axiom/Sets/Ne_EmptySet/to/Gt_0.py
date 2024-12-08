from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    return Greater(Card(A), 0)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra
    A = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Unequal(A, A.etype.emptySet))

    Eq << Sets.Ne_EmptySet.to.Ne_0.apply(Eq[0])

    Eq << Algebra.Ne_0.to.Gt_0.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-07-12
