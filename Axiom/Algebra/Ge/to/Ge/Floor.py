from util import *


@apply
def apply(given):
    x, y = given.of(GreaterEqual)
    return GreaterEqual(Floor(x), Floor(y))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x >= y)

    Eq << Algebra.Le.to.Le.Floor.apply(Eq[0].reversed).reversed





if __name__ == '__main__':
    run()
# created on 2021-12-27
# updated on 2021-12-27