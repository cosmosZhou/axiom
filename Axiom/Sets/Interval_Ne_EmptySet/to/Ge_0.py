from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    a, b = A.of(Interval)
    assert not A.left_open and not A.right_open
    return GreaterEqual(b - a, 0)


@prove
def prove(Eq):
    from Axiom import Sets

    a, b = Symbol(real=True, given=True)
    Eq << apply(Unequal(Interval(a, b), a.emptySet))

    Eq << ~Eq[1]

    Eq << Eq[-1] + a

    Eq << Sets.Lt.to.Eq_EmptySet.Interval.apply(Eq[-1])

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2019-09-23
