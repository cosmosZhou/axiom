from util import *


@apply
def apply(self, simplify=True):
    from Axiom.Algebra.Sum.eq.Add import associate
    return associate(All, self, simplify=simplify)


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    f, h = Function(real=True)
    Eq << apply(All[i:n]((f(i) > 0) & (h(i) > 0)))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.And.All.of.All_And)

    Eq << Eq[-1].this.rhs.apply(Algebra.All_And.given.And.All)


if __name__ == '__main__':
    run()

# created on 2018-12-22
