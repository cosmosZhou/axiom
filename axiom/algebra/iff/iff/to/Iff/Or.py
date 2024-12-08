from util import *


@apply
def apply(eq_ab, eq_xy):
    a, b = eq_ab.of(Iff)
    x, y = eq_xy.of(Iff)
    return Iff(a | x, b | y)


@prove
def prove(Eq):
    from Axiom import Algebra
    a, b, x, y = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))

    Eq << apply(Iff(a > 0, b > 0), Iff(x > 0, y > 0))

    Eq << Algebra.Iff.of.And.apply(Eq[-1])

    Eq << Algebra.Iff.to.Imply.apply(Eq[0])

    Eq << Algebra.Iff.to.Imply.apply(Eq[1])

    Eq << Algebra.Imply.Imply.to.Imply.Or.apply(Eq[-2], Eq[-1])

    Eq << Algebra.Iff.to.Given.apply(Eq[0])

    Eq << Algebra.Iff.to.Given.apply(Eq[1])

    Eq << Algebra.Given.Given.to.Given.Or.apply(Eq[-2], Eq[-1])

if __name__ == '__main__':
    run()
# created on 2019-02-09
