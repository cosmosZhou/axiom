from util import *


@apply
def apply(is_nonpositive_y, is_positive_x):
    x = is_positive_x.of(Expr > 0)
    y = is_nonpositive_y.of(Expr <= 0)
    return LessEqual(x * y, 0)


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(real=True)

    Eq << apply(y <= 0, x > 0)

    Eq << algebra.gt_zero.le_zero.imply.le_zero.apply(Eq[1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2018-07-18
