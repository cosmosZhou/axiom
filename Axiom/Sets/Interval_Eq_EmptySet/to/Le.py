from util import *


@apply
def apply(given):
    A = given.of(Equal[EmptySet])
    a, b = A.of(Interval)
    assert A.left_open or A.right_open
    return LessEqual(b, a)


@prove
def prove(Eq):
    from Axiom import Sets

    a, b = Symbol(real=True, given=True)
    Eq << apply(Equal(Interval(a, b, left_open=True), a.emptySet))

    Eq << Sets.Interval_Eq_EmptySet.to.Ge.apply(Eq[0])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2021-05-05
