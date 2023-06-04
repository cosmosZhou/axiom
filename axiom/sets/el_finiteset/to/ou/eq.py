from util import *


@apply
def apply(given):
    e, finiteset = given.of(Element[FiniteSet])

    return Or(*(Equal(e, s) for s in finiteset))


@prove
def prove(Eq):
    from axiom import algebra, sets

    e, a, b, c = Symbol(integer=True, given=True)
    Eq << apply(Element(e, {a, b, c}))

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(sets.el_finiteset.imply.ou.eq)

    Eq << Eq[-1].this.rhs.apply(sets.el_finiteset.given.ou.eq)


if __name__ == '__main__':
    run()
# created on 2023-05-30
