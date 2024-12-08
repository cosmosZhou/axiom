from util import *


@apply
def apply(self):
    a = self.of(Exp)
    res = a.of(Expr + Infinity * (Expr - 1)) or a.of(Expr + NegativeInfinity * (1 - Expr))
    a, X = res

    indices, limits = X.variables_with_limits()
    assert X[tuple(indices)] in FiniteSet(0, 1)

    return Equal(self, X * exp(a))


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True, positive=True)
    p = Function(bool=True)
    a = Symbol(real=True, shape=(n, n))
    i, j = Symbol(integer=True)
    Ξ = Lamda[j:n, i:n](Bool(p(i, j)))
    Eq << apply(exp(a - (1 - Ξ) * oo))

    a_quote = Symbol('a', a - (1 - Ξ) * oo)
    Eq << a_quote.this.definition

    Eq << Eq[-1][i, j]

    Eq << Eq[-1].this.find(Bool).apply(Algebra.Bool.eq.Piece, simplify=None)

    Eq << Eq[-1].this.find(1 - Piecewise).apply(Algebra.Add.eq.Piece)

    Eq << Eq[-1].this.find(Mul[Piecewise]).apply(Algebra.Mul.eq.Piece)

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.eq.Piece)

    Eq << Algebra.Eq.to.Eq.Exp.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Exp.eq.Piece)

    Eq << Eq[-1].this.rhs.apply(Algebra.Piece.eq.Mul.Bool)

    Eq << Algebra.Eq.to.Eq.Lamda.apply(Eq[-1], (j, 0, n), (i, 0, n))

    Eq << Eq[-1].this.lhs.arg.definition


if __name__ == '__main__':
    run()
# reference:
# Self-Attention with Relative Position Representations.pdf
# https://arxiv.org/abs/1803.02155
# created on 2020-12-27
# updated on 2023-06-18
