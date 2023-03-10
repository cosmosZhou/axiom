from util import *


@apply
def apply(is_nonpositive, is_negative):
    a = is_negative.of(Expr < 0)
    y = is_nonpositive.of(Expr <= 0)

    return Less(a + y, 0)


@prove
def prove(Eq):
    from axiom import algebra

    a, y = Symbol(real=True)
    Eq << apply(a <= 0, y < 0)

    Eq << algebra.le.lt.imply.lt.add.apply(Eq[0], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-12-11
