from util import *


@apply
def apply(given):
    x, y = given.of(Expr - Expr <= 0)
    return GreaterEqual(y, x)


@prove
def prove(Eq):
    from Axiom import Algebra

    a, b = Symbol(real=True, given=True)
    Eq << apply(GreaterEqual(0, a - b))

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Le_0.to.Ge)

    Eq << Eq[-1].this.rhs.apply(Algebra.Le_0.of.Ge)


if __name__ == '__main__':
    run()
# created on 2023-06-20
