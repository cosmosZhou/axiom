from util import *


@apply
def apply(is_positive_x, is_negative_y):
    x = is_positive_x.of(Expr >= 0)
    y = is_negative_y.of(Expr < 0)
    return LessEqual(x * y, 0)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    Eq << apply(x >= 0, y < 0)

    Eq << algebra.is_negative.is_nonnegative.imply.is_nonpositive.apply(Eq[1], Eq[0])


if __name__ == '__main__':
    run()