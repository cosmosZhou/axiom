from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    a, b = A.of(Interval)
    assert not A.left_open and not A.right_open
    return LessEqual(a - b, 0)


@prove
def prove(Eq):
    from Axiom import Sets

    a, b = Symbol(real=True, given=True)
    Eq << apply(Unequal(Interval(a, b), a.emptySet))

    Eq << Sets.Interval_Ne_EmptySet.of.Ge_0.apply(Eq[0])

    Eq << -Eq[-1]


if __name__ == '__main__':
    run()
# created on 2021-05-10
