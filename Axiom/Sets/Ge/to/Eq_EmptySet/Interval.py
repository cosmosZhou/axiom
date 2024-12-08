from util import *


@apply
def apply(given, left_open=False, right_open=False):
    a, b = given.of(GreaterEqual)
    assert left_open or right_open
    return Equal(Interval(a, b, left_open=left_open, right_open=right_open), a.emptySet)


@prove
def prove(Eq):
    from Axiom import Sets

    x, y = Symbol(real=True, given=True)
    Eq << apply(x >= y, left_open=True)

    Eq << ~Eq[1]

    Eq << Sets.Interval_Ne_EmptySet.to.Lt.apply(Eq[-1])

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2018-10-17
