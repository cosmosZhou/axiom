from util import *


@apply
def apply(given):
    x = given.of(Unequal[0])
    assert x.is_real
    return Greater(x ** 2, 0)


@prove
def prove(Eq):
    from axiom import algebra

    a = Symbol(real=True)
    Eq << apply(Unequal(a, 0))

    Eq << algebra.ne_zero.then.gt_zero.abs.apply(Eq[0])

    Eq << algebra.gt_zero.then.gt_zero.square.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-10-03
