from util import *


@apply
def apply(given):
    a, b = given.of(GreaterEqual)
    return Equal(Interval(a, b), a.set & b.set)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x, y = Symbol(real=True, given=True)
    Eq << apply(x >= y)

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=x > y)

    Eq.is_zero = (x > y).this.apply(Sets.Gt.to.Eq_EmptySet.Interval)

    Eq << Sets.IntersectFiniteSetS.subset.Interval.apply(x, y)

    Eq << Algebra.Cond.Imply.to.Imply.And.rhs.apply(Eq[-1], Eq.is_zero)

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Cond.to.Cond.subs)

    Eq << Eq[-1].this.rhs.apply(Sets.Subset.to.Eq.EmptySetSet, simplify=None)

    Eq <<= Eq[-1] & Eq.is_zero

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Eq.to.Eq.trans)

    Eq << Imply(x <= y, Equal(x, y), plausible=True)

    Eq << Algebra.Imply.of.Or.apply(Eq[-1])

    Eq <<= Eq[3] & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Cond.of.And.subs)





if __name__ == '__main__':
    run()
# created on 2018-09-15
# updated on 2023-08-26
