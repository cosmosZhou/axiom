from util import *


@apply
def apply(given):
    A = given.of(Equal[EmptySet])
    a, b = A.of(Interval)
    assert A.left_open or A.right_open
    return GreaterEqual(a - b, 0)


@prove
def prove(Eq):
    from axiom import sets
    a, b = Symbol(real=True, given=True)
    Eq << apply(Equal(Interval(a, b, left_open=True), a.emptySet))


    Eq << sets.interval_is_empty.given.ge.apply(Eq[0])

    Eq << Eq[-1] - b


if __name__ == '__main__':
    run()
