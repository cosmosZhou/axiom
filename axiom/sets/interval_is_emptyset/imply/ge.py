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

    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    Eq << apply(Equal(Interval(a, b, left_open=True), a.emptySet))

    Eq << ~Eq[1]

    Eq << sets.lt.imply.is_nonemptyset.apply(Eq[-1], right_open=False)

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()