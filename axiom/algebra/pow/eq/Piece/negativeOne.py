from util import *


@apply
def apply(self):
    n = self.of((-1) ** Expr)
    assert n.is_integer
    return Equal(self, Piecewise((1, Equal(n % 2, 0)), (-1, True)))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    n = Symbol(integer=True)
    Eq << apply((-1) ** n)

    Eq << Algebra.Cond_Piece.of.Or.apply(Eq[0])

    Eq << Eq[1].this.find(Equal & ~Equal).apply(Algebra.Eq_even.equ.Eq)

    Eq << Eq[-1].this.find(Unequal).apply(Algebra.Ne_0.equ.Eq_odd)

    Eq << Eq[-1].this.find(Equal & ~Equal).apply(Algebra.Eq_odd.equ.Eq)

    Eq << Sets.PowNegOne.el.FiniteSet.apply((-1) ** n)

    Eq << Sets.In_FiniteSet.to.Or.Eq.apply(Eq[-1])




if __name__ == '__main__':
    run()

# created on 2020-03-01
# updated on 2023-04-30
