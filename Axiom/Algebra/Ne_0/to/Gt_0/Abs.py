from util import *


@apply
def apply(given):
    x = given.of(Unequal[0])
    return Greater(abs(x), 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    a = Symbol(complex=True)
    Eq << apply(Unequal(a, 0))

    Eq << Algebra.Ne_0.to.Ne_0.Abs.apply(Eq[0])

    Eq << Algebra.Ne_0.to.Gt_0.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-03-18