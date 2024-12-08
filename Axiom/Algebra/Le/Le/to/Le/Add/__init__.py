from util import *


@apply
def apply(a_less_than_b, x_less_than_y):
    a, b = a_less_than_b.of(LessEqual)
    x, y = x_less_than_y.of(LessEqual)
    return LessEqual(a + x, b + y)


@prove
def prove(Eq):
    a, x, b, y = Symbol(real=True)

    Eq << apply(a <= b, x <= y)

    Eq << Eq[0] + Eq[1]


if __name__ == '__main__':
    run()

# created on 2019-09-27


del Abs
from . import Abs
