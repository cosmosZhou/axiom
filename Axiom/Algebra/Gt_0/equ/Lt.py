from util import *


@apply
def apply(given):
    x, y = given.of(Expr - Expr > 0)
    return Less(y, x)


@prove
def prove(Eq):
    from Axiom import Algebra

    a, b = Symbol(real=True, given=True)
    Eq << apply(Less(0, a - b))

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Gt_0.to.Lt)

    Eq << Eq[-1].this.rhs.apply(Algebra.Gt_0.of.Lt)


if __name__ == '__main__':
    run()
# created on 2023-06-20
