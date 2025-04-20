from util import *


@apply
def apply(all_le):
    (lhs, rhs), *limits = all_le.of(All[Greater])
    lhs = Lamda(lhs, *limits).simplify()
    rhs = Lamda(rhs, *limits).simplify()
    return lhs > rhs


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n,), real=True)
    i = Symbol(integer=True)
    Eq << apply(All[i:n](x[i] > y[i]))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.GtLamda.of.All_Gt)

    Eq << Eq[-1].this.rhs.apply(Algebra.All_Gt.given.Gt.Lamda)


if __name__ == '__main__':
    run()
# created on 2022-03-31
