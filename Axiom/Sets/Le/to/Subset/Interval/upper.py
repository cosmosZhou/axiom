from util import *


@apply
def apply(given, upper, left_open=False, right_open=False):
    a, b = given.of(LessEqual)
    kwargs = {'right_open' : right_open, 'left_open': left_open}
    return Subset(Interval(b, upper, **kwargs), Interval(a, upper, **kwargs))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x <= y, z, left_open=True)

    Eq << Sets.Subset.of.All_In.apply(Eq[1])

    Eq << Eq[-1].this.expr.apply(Sets.In_Interval.of.And)

    Eq << Algebra.All_And.of.And.All.apply(Eq[-1])

    Eq <<= Algebra.All.of.Or.apply(Eq[-2]), Algebra.All.of.Or.apply(Eq[-1])

    Eq <<= Eq[-2].this.find(NotElement).apply(Sets.NotIn_Interval.of.Or), Eq[-1].this.find(NotElement).apply(Sets.NotIn_Interval.of.Or)

    Eq << Algebra.Or.of.Or.apply(Eq[-1], slice(0, 3, 2))

    Eq << Sets.Or.of.NotIn.Interval.apply(Eq[-1])

    Eq << Sets.Le.to.Eq_EmptySet.Interval.apply(Eq[0], left_open=True)

    Eq << Eq[-2].subs(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2019-09-06
# updated on 2023-05-14
