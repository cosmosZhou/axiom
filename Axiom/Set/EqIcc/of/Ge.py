from util import *


@apply
def apply(given):
    a, b = given.of(GreaterEqual)
    return Equal(Interval(a, b), a.set & b.set)


@prove
def prove(Eq):
    from Axiom import Algebra, Set, Logic

    x, y = Symbol(real=True, given=True)
    Eq << apply(x >= y)

    Eq << Logic.Cond.given.And.Imp.split.apply(Eq[-1], cond=x > y)

    Eq.is_zero = (x > y).this.apply(Set.Eq_EmptySet.Icc.of.Gt)

    Eq << Set.InterFinsetS.subset.Icc.apply(x, y)

    Eq << Logic.Imp.And.of.Cond.Imp.rhs.apply(Eq[-1], Eq.is_zero)

    Eq << Eq[-1].this.rhs.apply(Logic.Cond.of.Eq.Cond.subs)

    Eq << Eq[-1].this.rhs.apply(Set.EqEmptySetSet.of.Subset, simplify=None)

    Eq <<= Eq[-1] & Eq.is_zero

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.of.Eq.Eq)

    Eq << Imply(x <= y, Equal(x, y), plausible=True)

    Eq << Logic.Imp.given.Or_Not.apply(Eq[-1])

    Eq <<= Eq[3] & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Cond.given.And.subs)





if __name__ == '__main__':
    run()
# created on 2018-09-15
# updated on 2023-08-26
