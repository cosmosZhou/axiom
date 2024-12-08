from util import *


@apply
def apply(self):
    n = self.of(KroneckerDelta[0, Expr % 2])
    return Equal(self, (1 + (-1) ** n) / 2)


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True)
    Eq << apply(KroneckerDelta(0, n % 2))

    Eq << Eq[0].this.find(Pow).apply(Algebra.Pow.eq.Piece.negativeOne)

    Eq << Eq[-1].this.find(Mul[Piecewise]).apply(Algebra.Mul.eq.Piece)

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.eq.Piece)

    Eq << Eq[-1].this.lhs.apply(Algebra.Delta.eq.Piece, swap=True)





if __name__ == '__main__':
    run()
# created on 2023-05-22
# updated on 2023-05-23
