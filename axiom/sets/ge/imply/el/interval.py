from util import *


@apply(simplify=None)
def apply(given):
    n, b = given.of(GreaterEqual)

    return Element(n, Interval(b, oo))


@prove
def prove(Eq):
    n, b = Symbol(real=True, given=True)
    Eq << apply(n >= b)

    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()

