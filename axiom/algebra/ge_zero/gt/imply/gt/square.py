from util import *


@apply
def apply(is_nonnegative, strict_greater_than):
    x = is_nonnegative.of(Expr >= 0)
    y, S[x] = strict_greater_than.of(Greater)
    return Greater(y ** 2, x ** 2)


@prove
def prove(Eq):
    from axiom import algebra

    x, a, y = Symbol(real=True)
    Eq << apply(x >= 0, y > x)

    Eq << Eq[1] + x

    Eq << Eq[0] * 2

    Eq << algebra.gt.ge.imply.gt.transit.apply(Eq[-1], Eq[-2])

    Eq << algebra.gt.imply.gt_zero.apply(Eq[1])

    Eq << algebra.gt_zero.gt_zero.imply.gt_zero.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add, deep=True)

    Eq << Eq[-1].this.apply(algebra.gt.transport, lhs=1)

    


if __name__ == '__main__':
    run()
# created on 2019-06-14
# updated on 2023-05-20
