from util import *


@apply
def apply(self):
    n, S[2] = self.of(Expr % Expr)
    assert n.is_integer
    return Equal(self, Piecewise((0, Equal(n % 2, 0)), (1, True)))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    n = Symbol(integer=True)
    Eq << apply(n % 2)

    Eq << Algebra.Cond_Piece.of.Or.apply(Eq[0])

    Eq << Sets.Or.of.In.FiniteSet.apply(Eq[-1])

    Eq << Sets.Mod.el.Range.apply(Eq[-1].lhs)

    Eq << Eq[-1].this.rhs.apply(Sets.Range.eq.FiniteSet)




if __name__ == '__main__':
    run()
# created on 2022-01-20
# updated on 2023-04-30
