from util import *


@apply
def apply(given):
    x = given.of(Ceiling > 0)
    return Greater(x, 0)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True, given=True)
    Eq << apply(Greater(Ceiling(x), 0))

    Eq << ~Eq[-1]

    Eq << algebra.le_zero.imply.ceiling_le_zero.apply(Eq[-1])
    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2018-10-30
