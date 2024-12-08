from util import *


@apply
def apply(self):
    a, b = self.of(FiniteSet & FiniteSet)
    return Equal(self, Piecewise((a.set, Equal(a, b)), (a.emptySet, True)))

@prove
def prove(Eq):
    from Axiom import Algebra

    a, b = Symbol(integer=True)
    Eq << apply(a.set & b.set)

    Eq << Algebra.Cond_Piece.of.Or.apply(Eq[0])

    Eq << Eq[-1].this.find(And).apply(Algebra.Eq.Cond.of.And.subs)





if __name__ == '__main__':
    run()
# created on 2018-09-11
# updated on 2023-08-26
