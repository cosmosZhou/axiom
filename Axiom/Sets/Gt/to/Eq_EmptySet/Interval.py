from util import *


@apply
def apply(given, left_open=False, right_open=False):
    a, b = given.of(Greater)

    return Equal(Interval(a, b, left_open=left_open, right_open=right_open), a.emptySet)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x > y)

    Eq << ~Eq[-1]

    Eq << Sets.Ne_EmptySet.to.Any_In.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(Sets.In_Interval.to.And)

    Eq << Eq[-1].this.expr.apply(Algebra.Le.Ge.to.Le.trans)

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2018-09-10
