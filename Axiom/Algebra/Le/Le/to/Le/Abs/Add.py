from util import *


@apply
def apply(x_less_than_a, y_less_than_b):
    abs_x, a = x_less_than_a.of(LessEqual)
    abs_y, b = y_less_than_b.of(LessEqual)

    x = abs_x.of(Abs)
    y = abs_y.of(Abs)

    return LessEqual(abs(x + y), a + b)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y, a, b = Symbol(real=True)
    Eq << apply(abs(x) <= a, abs(y) <= b)

    Eq << Algebra.Le_Abs.of.And.apply(Eq[-1])

    Eq << Algebra.Le.to.And.split.Abs.apply(Eq[0])

    Eq << Algebra.Le.to.And.split.Abs.apply(Eq[1])

    Eq <<= Eq[-4] + Eq[-2], Eq[-3] + Eq[-1]




if __name__ == '__main__':
    run()
# created on 2023-04-15
