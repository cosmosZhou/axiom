from util import *


@apply
def apply(a, b):
    return Subset(a.set & b.set, Interval(a, b))


@prove
def prove(Eq):
    from Axiom import Set, Algebra, Logic

    x, y = Symbol(real=True, given=True)
    Eq << apply(x, y)

    Eq << Eq[0].this.lhs.apply(Set.Inter.Finset.eq.Ite)

    Eq << Logic.Cond_Ite__Ite.given.And.ou.OrAndS.apply(Eq[-1])

    Eq << Eq[-1].this.find(And).apply(Algebra.Eq.Cond.given.And.subs)





if __name__ == '__main__':
    run()
# created on 2018-09-11
# updated on 2023-08-26
