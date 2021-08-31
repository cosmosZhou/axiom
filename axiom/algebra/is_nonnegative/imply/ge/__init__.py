from util import *


@apply
def apply(given):
    *x, y = given.of(Expr - Expr >= 0)
    x = Add(*x)
    return GreaterEqual(x, y)


@prove
def prove(Eq):
    a, b = Symbol(real=True, given=True)

    Eq << apply(LessEqual(0, a - b))

    Eq << Eq[0] + b

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
from . import scale
