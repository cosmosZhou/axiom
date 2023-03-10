from util import *


@apply
def apply(is_nonpositive, is_nonpositive1):
    a = is_nonpositive.of(Expr <= 0)
    y = is_nonpositive1.of(Expr <= 0)

    return LessEqual(a + y, 0)


@prove
def prove(Eq):
    from axiom import algebra

    a, y = Symbol(real=True)
    Eq << apply(a <= 0, y <= 0)

    Eq << algebra.le.le.imply.le.add.apply(Eq[0], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-12-08
