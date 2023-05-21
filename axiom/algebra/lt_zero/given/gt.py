from util import *


@apply
def apply(given):
    x, y = given.of(Expr - Expr < 0)
    return Greater(y, x)


@prove
def prove(Eq):
    from axiom import algebra

    a, b = Symbol(real=True, given=True)
    Eq << apply(Greater(0, a - b))

    Eq << algebra.gt.imply.lt_zero.apply(Eq[1]).reversed

    


if __name__ == '__main__':
    run()
# created on 2023-04-15
