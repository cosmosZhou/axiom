from util import *


@apply
def apply(given):
    e, S = given.of(NotElement)
    start, stop = S.of(Range)

    lower_bound = e < start
    upper_bound = e >= stop
    return Or(lower_bound, upper_bound)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    e, a, b = Symbol(integer=True, given=True)
    Eq << apply(NotElement(e, Range(a, b)))

    Eq << Algebra.Iff.of.And.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(Sets.NotIn_Range.to.Or)

    Eq << Eq[-1].this.rhs.apply(Sets.Or.to.NotIn.Range)



if __name__ == '__main__':
    run()
# created on 2021-12-17
