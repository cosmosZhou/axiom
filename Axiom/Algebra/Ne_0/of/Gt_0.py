from util import *


@apply
def apply(given):
    x = given.of(Unequal[0])
    return x > 0


@prove
def prove(Eq):
    from Axiom import Algebra
    a = Symbol(real=True)
    Eq << apply(Unequal(a, 0))

    Eq << Algebra.Gt_0.to.Ne_0.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2020-02-13