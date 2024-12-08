from util import *


@apply
def apply(given):
    x, y = given.of(LessEqual)
    return LessEqual(Floor(x), Floor(y))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x <= y)

    Eq << ~Eq[1]

    Eq << Algebra.Gt.to.Ge.strengthen.apply(Eq[-1])

    Eq << Algebra.LeFloor.apply(x)

    Eq << Algebra.Ge.Le.to.Ge.trans.apply(Eq[-2], Eq[-1])

    Eq << Algebra.Lt_Add_.Floor.One.apply(y)

    Eq << Algebra.Ge.Lt.to.Gt.trans.apply(Eq[-2], Eq[-1])

    Eq <<= Eq[-1] & Eq[0]





if __name__ == '__main__':
    run()
# created on 2021-12-27

from . import integer
