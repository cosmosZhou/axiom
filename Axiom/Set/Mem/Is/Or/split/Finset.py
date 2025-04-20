from util import *


@apply
def apply(given):
    x, finiteset = given.of(Element)
    finiteset = finiteset.of(FiniteSet)

    return Or(*(Equal(x, e) for e in finiteset))


@prove
def prove(Eq):
    from Axiom import Algebra, Set, Logic

    x, a, b = Symbol(real=True)
    Eq << apply(Element(x, {a, b}))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Set.OrEqS.of.Mem_Finset, simplify=False)

    Eq << Eq[-1].this.lhs.apply(Set.Mem.Finset.of.Or_Eq)


if __name__ == '__main__':
    run()

# created on 2020-08-15
