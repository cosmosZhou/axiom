from util import *


@apply
def apply(is_nonnegative, is_positive):
    a = is_nonnegative.of(Expr >= 0)
    y = is_positive.of(Expr > 0)

    return Greater(a + y, 0)


@prove
def prove(Eq):
    from axiom import algebra

    a, y = Symbol(real=True)
    Eq << apply(a >= 0, y > 0)

    Eq << algebra.ge.gt.imply.gt.add.apply(Eq[0], Eq[1])


if __name__ == '__main__':
    run()
# created on 2018-06-08
