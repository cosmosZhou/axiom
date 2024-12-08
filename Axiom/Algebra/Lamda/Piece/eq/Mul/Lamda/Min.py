from util import *


@apply
def apply(self):
    ((i, (j, S[i])), (S[j], S[j < i]), (S[0], S[True])), (S[j], S[0], n), (S[i], S[0], S[n]) = \
    self.of(
        Lamda[
            Piecewise[ExprCondPair[Greater],
                      ExprCondPair,
                      ExprCondPair
            ]
        ])
    return Equal(self, (1 - Identity(n)) * Lamda[j:n, i:n](Min(i, j)))


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True, positive=True)
    i, j = Symbol(integer=True)
    Eq << apply(Lamda[j:n, i:n](Piecewise((i, j > i), (j, j < i), (0, True))))

    i, j = Symbol(domain=Range(n))
    Eq << Algebra.Eq.of.Eq.getitem.apply(Eq[0], (i, j))

    Eq << Eq[-1].this.find(Min).apply(Algebra.Min.eq.Piece)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.eq.Piece)

    Eq << Eq[-1].this.rhs.simplify(wrt=i)

    Eq << Eq[-1].this.find(LessEqual).reversed

    Eq << Eq[-1].this.find(KroneckerDelta).apply(Algebra.Delta.eq.Piece)

    Eq << Eq[-1].this.find(Mul[Piecewise]).apply(Algebra.Mul.eq.Piece, simplify=None)

    Eq << Eq[-1].this.find(Add[Piecewise]).apply(Algebra.Add.eq.Piece, simplify=False)

    Eq << Eq[-1].this.find(Mul[Piecewise]).apply(Algebra.Mul.eq.Piece, simplify=False)

    Eq << Eq[-1].this.rhs.apply(Algebra.Piece.unnest, index=0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Piece.swap)

    Eq << Eq[-1].this.lhs.apply(Algebra.Piece.swap, -2)

    Eq << Eq[-1].this.lhs.apply(Algebra.Piece.And.invert, 0)

    Eq << Eq[-1].this.lhs.find(Equal).reversed





if __name__ == '__main__':
    run()
# created on 2019-10-18
# updated on 2022-04-01
