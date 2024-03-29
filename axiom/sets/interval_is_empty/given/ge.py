from util import *


@apply
def apply(given):
    A = given.of(Equal[EmptySet])
    a, b = A.of(Interval)
    assert A.left_open or A.right_open
    return GreaterEqual(a, b)


@prove
def prove(Eq):
    from axiom import sets

    a, b = Symbol(real=True, given=True)
    Eq << apply(Equal(Interval(a, b, left_open=True), a.emptySet))

    Eq << sets.ge.imply.is_empty.interval.apply(Eq[1], left_open=True)


if __name__ == '__main__':
    run()
# created on 2021-04-29
