from util import *


@apply
def apply(is_nonnegative, less_than):
    if not less_than.is_Less:
        less_than, is_nonnegative = given

    x = is_nonnegative.of(Expr >= 0)
    S[x], M = less_than.of(Less)

    return Equal(Floor(x), 0)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    Eq << apply(x >= 0, x < 1)

    Eq << algebra.then.floor_le.apply(x)

    Eq << algebra.le.lt.then.lt.trans.apply(Eq[-1], Eq[1])

    Eq << algebra.lt.then.le.strengthen.apply(Eq[-1])

    Eq << algebra.then.gt.floor.apply(x)

    Eq << algebra.gt.ge.then.gt.trans.apply(Eq[-1], Eq[0] - 1)

    Eq << algebra.gt.then.ge.strengthen.apply(Eq[-1])
    Eq <<= Eq[-4] & Eq[-1]


if __name__ == '__main__':
    run()
# created on 2018-10-21
