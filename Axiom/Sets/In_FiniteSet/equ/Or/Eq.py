from util import *


@apply
def apply(given):
    e, finiteset = given.of(Element[FiniteSet])

    return Or(*(Equal(e, s) for s in finiteset))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    e, a, b, c = Symbol(integer=True, given=True)
    Eq << apply(Element(e, {a, b, c}))

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Sets.In_FiniteSet.to.Or.Eq)

    Eq << Eq[-1].this.rhs.apply(Sets.In_FiniteSet.of.Or.Eq)


if __name__ == '__main__':
    run()
# created on 2023-05-30
