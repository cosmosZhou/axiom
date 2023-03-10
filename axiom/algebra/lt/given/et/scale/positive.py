from util import *


@apply
def apply(given, scale, div=False):
    lhs, rhs = given.of(Less)
    if div:
        lt = lhs / scale < rhs / scale
    else:
        lt = lhs * scale < rhs * scale
    return lt, scale > 0


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(Less(x, y), z, div=True)

    Eq << algebra.gt_zero.lt.imply.lt.mul.apply(Eq[2], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-08-20
