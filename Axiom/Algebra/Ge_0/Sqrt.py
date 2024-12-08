from util import *


@apply
def apply(given):
    x = given.of(Expr >= 0)
    return sqrt(x) >= 0


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True)
    Eq << apply(x >= 0)

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Ge_0.to.Ge_0.Sqrt)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ge_0.of.Ge_0.Sqrt)


if __name__ == '__main__':
    run()
# created on 2023-06-20
