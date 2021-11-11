from util import *


@apply
def apply(is_nonnegative, is_nonnegative1):
    a = is_nonnegative.of(Expr >= 0)
    y = is_nonnegative1.of(Expr >= 0)

    return GreaterEqual(a + y, 0)


@prove
def prove(Eq):
    from axiom import algebra

    a, y = Symbol(real=True)
    Eq << apply(y >= 0, a >= 0)

    Eq << algebra.ge.ge.imply.ge.add.apply(Eq[1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2018-06-07
# updated on 2018-06-07
