from util import *


@apply
def apply(is_nonnegative_x, is_positive_y):
    x = is_nonnegative_x.of(Expr >= 0)
    y = is_positive_y.of(Expr > 0)
    return GreaterEqual(x * y, 0)


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(real=True)

    Eq << apply(x >= 0, y > 0)

    Eq << algebra.is_positive.is_nonnegative.imply.is_nonnegative.apply(Eq[1], Eq[0])


if __name__ == '__main__':
    run()
