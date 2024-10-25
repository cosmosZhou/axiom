from util import *


@apply
def apply(is_positive_x, is_negative_y):
    x = is_positive_x.of(Expr >= 0)
    y = is_negative_y.of(Expr < 0)
    return LessEqual(x * y, 0)


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(real=True)

    Eq << apply(x >= 0, y < 0)

    Eq << algebra.lt_zero.ge_zero.then.le_zero.apply(Eq[1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2019-07-03
