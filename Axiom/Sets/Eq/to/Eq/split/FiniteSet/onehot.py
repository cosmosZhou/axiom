from util import *


@apply
def apply(given):
    (x, y), S[{0, 1}] = given.of(Equal[FiniteSet])
    return Equal(Matrix([x, y]), Matrix([1 - KroneckerDelta(0, x), KroneckerDelta(0, x)]))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x, y = Symbol(integer=True)
    Eq << apply(Equal({x, y}, {0, 1}))

    Eq << Algebra.Eq.of.And.split.Matrix.apply(Eq[1])



    Eq << Element(x, {x, y}, plausible=True)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Sets.In.to.Eq.Delta.Zero.apply(Eq[-1])

    Eq.x_equality = -Eq[-1] + 1

    Eq << Eq.x_equality.reversed

    Eq << Sets.Eq.to.Eq.split.FiniteSet.Add.apply(Eq[0])

    Eq << Eq[-1] + Eq.x_equality

    Eq << Eq[-1].this.apply(Algebra.Eq.simp.terms.common)

    Eq << Algebra.Eq_0.to.Eq.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-04-02
