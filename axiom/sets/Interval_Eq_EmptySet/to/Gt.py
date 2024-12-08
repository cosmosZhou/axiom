from util import *


@apply
def apply(given):
    A = given.of(Equal[EmptySet])
    a, b = A.of(Interval)
    assert not A.left_open and not A.right_open
    return Greater(a, b)


@prove
def prove(Eq):
    from Axiom import Sets

    a, b = Symbol(real=True, given=True)
    Eq << apply(Equal(Interval(a, b), a.emptySet))

    Eq << ~Eq[1]

    Eq << Sets.Le.to.Subset.Interval.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[0])

    Eq << Sets.Subset.to.Eq_EmptySet.apply(Eq[-1])

    Eq << Sets.Eq.Eq.to.Eq.Union.apply(Eq[0], Eq[-1])
    Eq << Eq[-1].this.lhs.apply(Sets.Union.eq.Interval)



if __name__ == '__main__':
    run()
# created on 2021-05-05
