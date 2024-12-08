from util import *


@apply
def apply(ou):
    x, y = ou.of(Unequal[0] | Unequal[0])
    r = sqrt(x ** 2 + y ** 2)
    return Greater(r, 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(real=True)
    Eq << apply(Unequal(x, 0) | Unequal(y, 0))

    Eq << Algebra.Or_Ne_0.to.Gt_.Add.Zero.Square.apply(Eq[0])
    Eq << Algebra.Gt_0.to.Gt_0.Sqrt.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-07-17
