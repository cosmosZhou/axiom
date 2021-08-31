from util import *


@apply
def apply(greater_than, less_than):
    x, a = greater_than.of(GreaterEqual)
    y, b = less_than.of(GreaterEqual)

    return GreaterEqual((x - a) * (y - b), 0)


@prove
def prove(Eq):
    from axiom import algebra
    x, y, a, b = Symbol(real=True)

    Eq << apply(x >= a, y >= b)

    Eq << Eq[0] - a

    Eq << Eq[1] - b

    Eq << algebra.is_nonnegative.is_nonnegative.imply.is_nonnegative.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
