from util import *


@apply
def apply(given, pivot):
    x, a = given.of(GreaterEqual)
    assert pivot.is_real
    return Or(GreaterEqual(x, a) & LessEqual(x, pivot), Greater(x, pivot))


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x >= y, z)

    Eq << ~Eq[-1]

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[0], Eq[-1], invert=True)


if __name__ == '__main__':
    run()
# created on 2018-07-04
