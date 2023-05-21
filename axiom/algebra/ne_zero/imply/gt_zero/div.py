from util import *


@apply
def apply(given):
    x = given.of(Unequal[0])
    assert x >= 0
    return Greater(1 / x, 0, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    a = Symbol(nonnegative=True)
    Eq << apply(Unequal(a, 0))

    Eq << algebra.ne_zero.imply.gt_zero.apply(Eq[0])

    Eq << algebra.gt_zero.imply.gt_zero.div.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-04-22
