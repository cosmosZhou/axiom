from util import *


@apply
def apply(is_nonnegative, is_nonpositive_y):
    x = is_nonnegative.of(Expr >= 0)
    y = is_nonpositive_y.of(Expr <= 0)
    return LessEqual(x * y, 0)


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(real=True)

    Eq << apply(x >= 0, y <= 0)

    Eq << algebra.le_zero.ge_zero.then.le_zero.apply(Eq[1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2018-02-10
