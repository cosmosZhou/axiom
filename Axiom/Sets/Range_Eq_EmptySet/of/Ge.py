from util import *


@apply
def apply(given):
    A = given.of(Equal[EmptySet])
    a, b = A.of(Range)
    return GreaterEqual(a, b)


@prove
def prove(Eq):
    from Axiom import Sets

    a, b = Symbol(integer=True, given=True)
    Eq << apply(Equal(Range(a, b), a.emptySet))

    Eq << Sets.Ge.to.Eq_EmptySet.Range.apply(Eq[-1])






if __name__ == '__main__':
    run()
# created on 2021-06-15
