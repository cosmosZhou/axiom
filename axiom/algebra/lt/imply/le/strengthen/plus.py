from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Less)
    assert lhs.is_integer and rhs.is_integer
    return LessEqual(lhs + 1, rhs)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(integer=True, given=True)
    Eq << apply(x < y)

    Eq << algebra.lt.imply.le.strengthen.apply(Eq[0])

    Eq << Eq[-1] + 1


if __name__ == '__main__':
    run()
# created on 2018-10-14
