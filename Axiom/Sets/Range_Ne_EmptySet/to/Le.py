from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    a, b = A.of(Range)
    return LessEqual(a, b)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b = Symbol(integer=True, given=True)
    Eq << apply(Unequal(Range(a, b), a.emptySet))

    Eq << Sets.Range_Ne_EmptySet.to.Lt.apply(Eq[0])
    Eq << Algebra.Lt.to.Le.relax.apply(Eq[-1])



if __name__ == '__main__':
    run()
# created on 2021-06-23
