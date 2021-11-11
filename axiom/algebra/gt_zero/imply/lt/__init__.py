from util import *


@apply
def apply(given):
    x, y = given.of(Expr - Expr > 0)
    return Less(y, x)


@prove
def prove(Eq):
    a, b = Symbol(real=True, given=True)

    Eq << apply(Less(0, a - b))

    Eq << Eq[0] + b

    Eq << Eq[-1]


if __name__ == '__main__':
    run()
from . import scale
# created on 2020-04-30
# updated on 2020-04-30
