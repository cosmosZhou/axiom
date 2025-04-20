from util import *


@apply
def apply(given, lower, left_open=False, right_open=False):
    a, b = given.of(LessEqual)
    kwargs = {'right_open' : right_open, 'left_open': left_open}
    return Subset(Interval(lower, a, **kwargs), Interval(lower, b, **kwargs))


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x <= y, z, left_open=True)

    Eq << Set.Subset.given.All_Mem.apply(Eq[1])

    Eq << Eq[-1].this.expr.apply(Set.Mem_Icc.given.And)

    Eq << Algebra.All_And.given.And.All.apply(Eq[-1])

    Eq <<= Algebra.All.given.Or.apply(Eq[-2]), Algebra.All.given.Or.apply(Eq[-1])

    Eq <<= Eq[-2].this.args[1].apply(Set.NotMem_Icc.given.Or), Eq[-1].this.find(NotElement).apply(Set.NotMem_Icc.given.Or)

    Eq << Algebra.Or.given.Or.apply(Eq[-1], slice(0, 2))

    Eq << Set.Or.given.NotMem.Icc.apply(Eq[-1])

    Eq << Set.Eq_EmptySet.Icc.of.Le.apply(Eq[0], left_open=True)

    Eq << Eq[-2].subs(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2019-07-09
# updated on 2023-05-19
