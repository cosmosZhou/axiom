from util import *


@apply
def apply(given):
    x, y = given.of(LessEqual)
    return LessEqual(Floor(x), Floor(y))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x <= y)

    Eq << ~Eq[1]

    Eq << algebra.gt.then.ge.strengthen.apply(Eq[-1])

    Eq << algebra.then.floor_le.apply(x)

    Eq << algebra.ge.le.then.ge.trans.apply(Eq[-2], Eq[-1])

    Eq << algebra.then.lt.floor.apply(y)

    Eq << algebra.ge.lt.then.gt.trans.apply(Eq[-2], Eq[-1])

    Eq <<= Eq[-1] & Eq[0]





if __name__ == '__main__':
    run()
# created on 2021-12-27

from . import integer
