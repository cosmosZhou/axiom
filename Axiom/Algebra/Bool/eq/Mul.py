from util import *


@apply
def apply(self):
    eqs = self.of(Bool[And])
    return Equal(self, Mul(*(Bool(eq)for eq in eqs)))


@prove
def prove(Eq):
    from Axiom import Algebra
    x, y, a, b = Symbol(real=True)
    Eq << apply(Bool((x > y) & (a > b)))

    Eq << Eq[0].this.rhs.find(Bool).apply(Algebra.Bool.eq.Piece)

    Eq << Eq[-1].this.rhs.find(Bool).apply(Algebra.Bool.eq.Piece)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.Piece.eq.Piece)

    Eq << Eq[-1].this.rhs.apply(Algebra.Piece.unnest, index=0)

    Eq << Eq[-1].this.lhs.apply(Algebra.Bool.eq.Piece)


if __name__ == '__main__':
    run()

# created on 2018-02-14
