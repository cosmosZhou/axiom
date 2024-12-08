from util import *


@apply
def apply(given):
    A = given.of(Equal[EmptySet])
    a, b = A.of(Range)
    return GreaterEqual(a - b, 0)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b = Symbol(integer=True, given=True)
    Eq << apply(Equal(Range(a, b), a.emptySet))

    Eq << Sets.Range_Eq_EmptySet.to.Ge.apply(Eq[0])
    Eq << Algebra.Ge.to.Ge_0.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-06-18
