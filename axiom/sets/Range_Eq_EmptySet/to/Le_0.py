from util import *


@apply
def apply(given):
    A = given.of(Equal[EmptySet])
    a, b = A.of(Range)
    return LessEqual(b - a, 0)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b = Symbol(integer=True, given=True)
    Eq << apply(Equal(Range(a, b), a.emptySet))

    Eq << Sets.Range_Eq_EmptySet.to.Le.apply(Eq[0])

    Eq << Algebra.Le.to.Le_0.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-06-19
