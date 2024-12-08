from util import *


@apply
def apply(given):
    x = given.of(Unequal[0])
    assert x.is_real
    return Greater(x ** 2, 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    a = Symbol(real=True)
    Eq << apply(Unequal(a, 0))

    Eq << Algebra.Ne_0.to.Gt_0.Abs.apply(Eq[0])

    Eq << Algebra.Gt_0.to.Gt_0.Square.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-10-03
