from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)
    return Element(sqrt(x), Reals)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x = Symbol(real=True, given=True)
    Eq << apply(x > 0)

    Eq << Algebra.Gt_0.to.Ge_0.apply(Eq[0])

    Eq << Sets.Ge_0.to.Sqrt_is_real.apply(Eq[-1], simplify=None)


if __name__ == '__main__':
    run()
# created on 2021-04-20
