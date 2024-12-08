from util import *


@apply
def apply(given):
    A = given.of(Equal[EmptySet])
    a, b = A.of(Interval)
    assert not A.left_open and not A.right_open
    return Greater(a - b, 0)


@prove
def prove(Eq):
    from Axiom import Sets
    a, b = Symbol(real=True, given=True)
    Eq << apply(Equal(Interval(a, b), a.emptySet))

    Eq << Sets.Interval_Eq_EmptySet.of.Gt.apply(Eq[0])

    Eq << Eq[-1] - b


if __name__ == '__main__':
    run()
# created on 2021-05-01
