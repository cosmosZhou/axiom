from util import *


@apply
def apply(given):
    x = given.of(Expr < 0)

    return Less(Floor(x), 0)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol(real=True, given=True)
    Eq << apply(x < 0)

    Eq << algebra.lt_zero.then.le_zero.apply(Eq[0])

    Eq << algebra.le_zero.then.floor_le_zero.apply(Eq[-1])

    Eq << ~Eq[1]

    Eq <<= Eq[-1] & Eq[-2]

    Eq << sets.floor_is_zero.then.el.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2020-01-20
