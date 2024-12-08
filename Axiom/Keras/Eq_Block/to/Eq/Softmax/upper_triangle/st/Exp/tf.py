from util import *


@apply
def apply(eq):
    (((((A, i), (S[i], (S[i], (n, u)))), (S[i], S[0], (S[1], S[n],  S[-Min(n, u)]))), (((S[A], S[i + n - Min(n, u) + 1]), (S[i + n - Min(n, u) + 1], S[n])), (S[i], S[0], (n, u)))), (S[A[i][i:Min(n, i + u)]], (S[i], S[0], S[n]))), z = \
    eq.of(Equal[
        BlockMatrix[
            Lamda[Exp[Sliced[Indexed, Tuple[Add[Min]]]], Tuple[Add]],
            Lamda[
                BlockMatrix[
                    Exp[Sliced[Indexed]],
                    ZeroMatrix],
                Tuple[Min - 1]]] / Lamda[OneMatrix * ReducedSum[Exp]]])

    assert n >= 2 and u >= 2

    breadth = Min(u, n) - 1
    return Equal(softmax(A + (BandPart[0, u - 1](OneMatrix(n, n)) - 1) * oo), BlockMatrix(
        Lamda[i:n - breadth](BlockMatrix(ZeroMatrix(i), z[i], ZeroMatrix(n - 1 - i - breadth))),
        Lamda[i:breadth](BlockMatrix(ZeroMatrix(n - breadth + i), z[i + n - breadth, :breadth - i]))))


@prove
def prove(Eq):
    from Axiom import Keras, Algebra, Sets

    n, u = Symbol(domain=Range(2, oo))
    A = Symbol(shape=(n, n), real=True)
    i = Symbol(integer=True)
    z = Symbol(shape=(n, Min(u, n)), real=True)
    Eq << apply(Equal(z, BlockMatrix(
        Lamda[i:n - Min(u, n) + 1](Exp(A[i, i:i + Min(u, n)])),
        Lamda[i:Min(u, n) - 1](BlockMatrix(Exp(A[i + n - Min(u, n) + 1, n - Min(u, n) + i + 1:]), ZeroMatrix(i + 1)))) / Lamda[i:n](OneMatrix(Min(u, n)) * ReducedSum(Exp(A[i, i:Min(n, i + u)])))))

    i = Eq[1].find(Lamda).variable
    Ξ = Symbol(Eq[1].find(BandPart))
    Eq.ksi_def = Ξ.this.definition

    Eq << Algebra.Mul.eq.Exp.oo.apply(exp(A) * Ξ).reversed

    a_quote = Symbol(Eq[-1].lhs.arg)
    Eq.a_quote_def = a_quote.this.definition

    Eq.a_quote_exp = Eq[-1].subs(Eq.a_quote_def.reversed)

    z = Symbol(Eq[1].lhs)
    Eq.z_def = z.this.definition

    Eq << Eq.z_def.subs(Eq.ksi_def.reversed, Eq.a_quote_def.reversed)

    Eq << Eq[-1][i]

    Eq << Eq[-1].this.rhs.apply(Keras.Softmax.eq.Mul.ReducedSum)

    Eq.zi_def = Eq[-1].this.rhs.subs(Eq.a_quote_exp[i])

    Eq << Eq.ksi_def[i].this.find(BandPart).defun()

    Eq.ksi_def = Eq[-1].this.rhs.expr.apply(Algebra.Bool.eq.Piece)

    Eq << Eq.zi_def.find(ReducedSum).this.subs(Eq.ksi_def)

    Eq << Eq[-1].this.rhs.apply(Algebra.ReducedSum.eq.Sum)

    Eq << Eq[-1].this.find(Element).apply(Sets.In.Add, i)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.ReducedSum)

    Eq << Eq[-1].this(i).find(Max).simplify()

    Eq << Eq.zi_def.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Indexed).defun()

    Eq << Eq[-1].this.find(BandPart).defun()

    Eq << Eq[-1].this.find(Bool).apply(Algebra.Bool.eq.Piece)

    j = Eq.ksi_def.rhs.variable
    Eq << Eq[-1][j]

    Eq.zij_def = Eq[-1].this.find(Mul).apply(Algebra.Mul.eq.Piece)

    z_dquote = Symbol('z^\"', Eq[1].rhs)
    Eq.z_dquote_def = z_dquote.this.definition

    Eq.zi_dquote_def = Eq.z_dquote_def[i]

    Eq << Eq.zi_dquote_def[j]

    Eq << Eq[-1].this.find(ExprCondPair).expr.apply(Algebra.Piece.swap, i=0)

    Eq << Eq[-1].this.find(And).apply(Sets.Cond.Cond.equ.In.Range, simplify=None)

    Eq << Eq[-1].this.find(Element).apply(Sets.In.Sub, i, simplify=None)

    Eq << Eq[-1].this.rhs.apply(Algebra.Piece.unnest)

    Eq.zij_dquote_def = Eq[-1].this.rhs.apply(Algebra.Piece.swap, 1)

    Eq.zi_quote_def = Eq[0][i]

    Eq << Eq.zi_quote_def[j - i]

    Eq << Eq.zij_dquote_def.this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this(j).find(Symbol < Symbol).simplify()

    Eq << Eq[-1].this.find(And).apply(Algebra.And.collect, cond=Eq[-1].find(Element))

    Eq << Eq[-1].this(i, j).find(And).apply(Sets.Or.Or.equ.In.Range.BandPart.upper.offset)

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq.zij_def, Eq[-1])

    Eq << Algebra.Eq.to.Eq.Lamda.apply(Eq[-1], (j, 0, n), (i, 0, n))

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq.z_dquote_def, Eq[-1])

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq.z_def, Eq[-1])





if __name__ == '__main__':
    run()
# created on 2022-01-01
# updated on 2022-01-23
