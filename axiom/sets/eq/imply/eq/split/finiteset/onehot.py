from util import *


@apply
def apply(given):
    (x, y), S[{0, 1}] = given.of(Equal[FiniteSet])
    return Equal(Matrix([x, y]), Matrix([1 - KroneckerDelta(0, x), KroneckerDelta(0, x)]))


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, y = Symbol(integer=True)
    Eq << apply(Equal({x, y}, {0, 1}))

    Eq << algebra.eq.given.et.split.matrix.apply(Eq[1])



    Eq << Element(x, {x, y}, plausible=True)

    Eq << Eq[-1].subs(Eq[0])

    Eq << sets.el.imply.eq.delta.zero.apply(Eq[-1])

    Eq.x_equality = -Eq[-1] + 1

    Eq << Eq.x_equality.reversed

    Eq << sets.eq.imply.eq.split.finiteset.add.apply(Eq[0])

    Eq << Eq[-1] + Eq.x_equality

    Eq << Eq[-1].this.apply(algebra.eq.simplify.terms.common)

    Eq << algebra.is_zero.imply.eq.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-04-02
