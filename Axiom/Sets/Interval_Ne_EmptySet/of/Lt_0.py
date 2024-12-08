from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    a, b = A.of(Interval)
    assert A.left_open or A.right_open
    return Less(a - b, 0)


@prove
def prove(Eq):
    from Axiom import Sets

    a, b = Symbol(real=True, given=True)
    Eq << apply(Unequal(Interval(a, b, left_open=True), a.emptySet))

    Eq << Sets.Interval_Ne_EmptySet.of.Gt_0.apply(Eq[0])

    Eq << -Eq[-1]


if __name__ == '__main__':
    run()
# created on 2021-05-11
