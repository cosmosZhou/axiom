from util import *


@apply
def apply(eq_R, x):
    from Axiom.Keras.Eq_Lamda.to.Dot.eq.Lamda.position_representation.rotary import extract
    (Ri, d), b, (i, j, k) = extract(eq_R)
    return Equal(
        Ri.T @ x,
        Lamda[j:d](
            Piecewise(
                (x[j] * cos(i / b ** (j / d)) + x[j + 1] * sin(i / b ** (j / d)), Equal(j % 2, 0)),
                (x[j] * cos(i / b ** ((j - 1) / d)) - x[j - 1] * sin(i / b ** ((j - 1) / d)), True))))


@prove
def prove(Eq):
    from Axiom import Discrete, Algebra, Sets
    from Axiom.Keras.Eq_Lamda.to.Dot.eq.Lamda.position_representation.rotary import rotary_matrix
    # n denotes sequence length (seq_length)
    # b denotes 10000
    n, b = Symbol(integer=True, positive=True)
    # d denotes embedding size which must be even
    d = Symbol(integer=True, positive=True, even=True)
    # x_i denotes token embedding at index i (ie, x denotes sentence embedding)
    x = Symbol(shape=(n, d), real=True)
    # R denotes rotary matrix
    R = Function(shape=(d, d), real=True)
    # i denotes token index
    # j denotes row index
    # k denotes column index
    i, j, k = Symbol(integer=True)
    Eq << apply(Equal(R(i), rotary_matrix(d, b, i, j, k)), x[i])

    Eq << Eq[0].T @ x[i]

    Eq << Eq[-1].this.rhs.apply(Discrete.Dot.eq.Lamda)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.halve)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.halve)

    Eq <<= Eq[-1].find(Element).this.apply(Sets.In.Range.Mul.dilated, 2), \
        Eq[-1].find(Piecewise[2]).find(Element).this.apply(Sets.In.Range.Mul.dilated, 2).this.rhs.apply(Sets.In.Add, 1)

    Eq <<= Eq[-2].this.rhs.apply(Sets.In_Range.equ.And.split.Range),\
        Eq[-1].this.rhs.apply(Sets.In_Range.equ.And.split.Range)

    Eq << Eq[-5].subs(*Eq[-2:])

    Eq << Eq[-1].this.find(Piecewise).apply(Algebra.Piece.nest, pivot=slice(1, None))

    Eq << Eq[-1].this.find(Piecewise[2]).apply(Algebra.Piece.nest, pivot=slice(1, None))

    Eq << Eq[-1].this.find(Piecewise[2]).apply(Algebra.Piece.nest, pivot=slice(1, None))

    Eq << Eq[-1].this.find(Piecewise).apply(Algebra.Piece.nest, pivot=slice(1, None))

    Eq << Eq[-1].find(Equal[1]).this.apply(Algebra.Eq_odd.equ.Ne.Zero)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.expr.args[1:3].apply(Algebra.Add.Piece.eq.Piece, simplify=None)

    Eq << Eq[-1].this.rhs.expr.args[::2].apply(Algebra.Add.Piece.eq.Piece, simplify=None)

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.Add.Piece.eq.Piece, simplify=None)

    Eq << Eq[-1].this.rhs().expr.args[0]().find(Element).simplify()

    Eq << Eq[-1].this.rhs().expr.args[0]().find(Element).simplify()

    Eq << Eq[-1].this.rhs().expr.args[1]().find(Element).simplify()

    Eq << Eq[-1].this.rhs().expr.args[1]().find(Element).simplify()

    Eq << Eq[-1].find(Mul[Add]).this.apply(Algebra.Mul.scale, 2)

    Eq << Eq[-2].subs(Eq[-1])

    # reference:
    # https://arxiv.org/pdf/2104.09864.pdf#page=7




if __name__ == '__main__':
    run()
# created on 2023-06-03
# updated on 2023-09-16
