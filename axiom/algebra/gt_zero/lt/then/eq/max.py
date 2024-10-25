from util import *


@apply
def apply(is_positive, lt):
    x = is_positive.of(Expr > 0)
    S[x], y = lt.of(Less)

    return Equal(Max(y ** 2, x ** 2), y ** 2)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    Eq << apply(x > 0, x < y)

    Eq << Eq[-1] - y ** 2

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.max)

    Eq << algebra.gt_zero.lt.then.lt.square.apply(Eq[0], Eq[1])

    Eq << algebra.lt.then.lt_zero.apply(Eq[-1])

    Eq << algebra.lt.then.eq.max.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-08-28
