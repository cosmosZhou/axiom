from util import *


@apply
def apply(x_less_than_y, x_greater_than_y_minus):
    x, y = x_less_than_y.of(LessEqual)
    S[x], S[-y] = x_greater_than_y_minus.of(GreaterEqual)
    return LessEqual(abs(x), abs(y))


@prove
def prove(Eq):
    from axiom import algebra
    y, x = Symbol(real=True)

    Eq << apply(x <= y, x >= -y)

    Eq << algebra.le.ge.then.ge.trans.apply(Eq[0], Eq[1])

    Eq << Eq[-1] + y

    Eq << Eq[-1] / 2

    Eq << algebra.ge_zero.then.eq.abs.apply(Eq[-1])

    Eq << algebra.le.ge.then.le.abs.apply(Eq[0], Eq[1])

    Eq << Eq[-1] + Eq[-2].reversed

    Eq << Eq[-1].this.apply(algebra.le.simplify.terms.common)


if __name__ == '__main__':
    run()
# created on 2019-05-30
