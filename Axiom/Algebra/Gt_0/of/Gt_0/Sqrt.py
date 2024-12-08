from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)
    return sqrt(x) > 0


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True)
    Eq << apply(x > 0)

    Eq << Algebra.Gt_0.Gt_0.to.Gt_0.apply(Eq[1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2023-06-20
