from util import *


@apply
def apply(given):
    e, finiteset = given.of(Element[FiniteSet])

    return Or(*(Equal(e, s) for s in finiteset))


@prove
def prove(Eq):
    from Axiom import Algebra, Set, Logic

    e, a, b, c = Symbol(integer=True, given=True)
    Eq << apply(Element(e, {a, b, c}))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Set.Or.Eq.of.Mem_Finset)

    Eq << Eq[-1].this.rhs.apply(Set.Mem_Finset.given.Or.Eq)


if __name__ == '__main__':
    run()
# created on 2023-05-30
