from util import *


@apply
def apply(x1_less_than_y, y_less_than_x):
    y, x = y_less_than_x.of(LessEqual)
    S[x - 1], S[y] = x1_less_than_y.of(Less)
    assert y.is_integer

    return Equal(y, floor(x))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True)
    y = Symbol(integer=True)

    Eq << apply(x - 1 < y, y <= x)

    Eq << Eq[0] - y + 1

    Eq << (Eq[1] - y).reversed

    Eq << algebra.ge_zero.lt.imply.eq.frac.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.rhs.apply(algebra.frac.to.add)


if __name__ == '__main__':
    run()
# created on 2019-03-08
