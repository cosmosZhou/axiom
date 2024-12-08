from util import *


@apply
def apply(given):
    x, finiteset = given.of(Element)
    finiteset = finiteset.of(FiniteSet)

    return Or(*(Equal(x, e) for e in finiteset))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x, a, b = Symbol(real=True)
    Eq << apply(Element(x, {a, b}))

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Sets.In.to.Or.split.FiniteSet.two, simplify=False)

    Eq << Eq[-1].this.rhs.apply(Sets.Or_Eq.to.In.FiniteSet)


if __name__ == '__main__':
    run()

# created on 2020-08-15
