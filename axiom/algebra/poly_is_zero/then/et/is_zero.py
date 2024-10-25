from util import *


@apply
def apply(given):
    xx, yy = given.of(Equal[Add, 0])

    x = xx.of(Expr ** 2)
    assert x.is_extended_real

    y = yy.of(Expr ** 2)
    assert y.is_extended_real

    return Equal(x, 0), Equal(y, 0)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(Equal(x * x + y * y, 0))

    Eq << algebra.poly_is_zero.then.is_zero.st.square.apply(Eq[0], 0)
    Eq << algebra.poly_is_zero.then.is_zero.st.square.apply(Eq[0], 1)


if __name__ == '__main__':
    run()
# created on 2018-06-09
