from util import *


@apply
def apply(given, left_open=False, right_open=False):
    a, b = given.of(Less)

    return Equal(Interval(b, a, left_open=left_open, right_open=right_open), a.emptySet)


@prove
def prove(Eq):
    from axiom import sets

    x, y = Symbol(real=True, given=True)
    Eq << apply(x < y)

    Eq << Eq[0].reversed

    Eq << sets.gt.imply.interval_is_empty.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-09-22
# updated on 2019-09-22
