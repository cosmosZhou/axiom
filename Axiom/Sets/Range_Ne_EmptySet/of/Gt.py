from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    a, b = A.of(Range)
    return Greater(b, a)


@prove
def prove(Eq):
    from Axiom import Sets

    a, b = Symbol(integer=True, given=True)
    Eq << apply(Unequal(Range(a, b), a.emptySet))

    Eq << Sets.Gt.to.Range_Ne_EmptySet.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2021-06-19