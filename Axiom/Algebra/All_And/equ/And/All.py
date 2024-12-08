from util import *


@apply
def apply(self, simplify=True):
    from Axiom.Algebra.Sum.eq.Add import associate
    return associate(All, self, simplify=simplify)


@prove
def prove(Eq):
    from Axiom import Algebra

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    f, h = Function(real=True)
    Eq << apply(All[i:n]((f(i) > 0) & (h(i) > 0)))

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.All_And.to.And.All)

    Eq << Eq[-1].this.rhs.apply(Algebra.All_And.of.And.All)


if __name__ == '__main__':
    run()

# created on 2018-12-22
