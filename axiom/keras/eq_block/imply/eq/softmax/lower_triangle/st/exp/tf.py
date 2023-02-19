from util import *


@apply
def apply(eq):
    (((((A, i), (S[0], S[i + 1])), (S[i], S[0], l)), (S[A[i + l - 1, i:i + l]], (S[i], S[0], (n, S[l])))), (S[A[i, relu(i - l + 1):i + 1]], (S[i], S[0], S[n]))), z = \
    eq.of(Equal[
        BlockMatrix[
            Lamda[BlockMatrix[
                ZeroMatrix,
                Exp[Sliced[Indexed]]],
                Tuple[Expr - 1]],
            Lamda[Exp, Tuple[Expr + 1 - Expr]]] / Lamda[OneMatrix * ReducedSum[Exp]]])

    assert n >= 2 and l >= 2 and l <= n

    return Equal(softmax(A + (BandPart[l - 1, 0](OneMatrix(n, n)) - 1) * oo), BlockMatrix(
        Lamda[i:l - 1](BlockMatrix(z[i, l - 1 - i:], ZeroMatrix(n - 1 - i))),
        Lamda[i:n - l + 1](BlockMatrix(ZeroMatrix(i), z[i + l - 1], ZeroMatrix(n - i - l)))))


@prove
def prove(Eq):
    from axiom import keras, algebra, sets

    n = Symbol(domain=Range(2, oo))
    l = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    i = Symbol(integer=True)
    z = Symbol(shape=(n, l), real=True)
    Eq << apply(Equal(z, BlockMatrix(
            Lamda[i:l - 1](BlockMatrix(ZeroMatrix(l - i - 1), Exp(A[i, :i + 1]))),
            Lamda[i:n - l + 1](Exp(A[i + l - 1, i:i + l]))) / Lamda[i:n](OneMatrix(l) * ReducedSum(Exp(A[i, relu(i + 1 - l):i + 1])))))

    i = Eq[1].find(Lamda).variable
    Ξ = Symbol(Eq[1].find(BandPart))
    Eq.ksi_def = Ξ.this.definition

    Eq << keras.imply.eq.bert.mask.theorem.apply(A, Ξ, add=True)

    a_quote = Symbol(Eq[-1].lhs.arg)
    Eq.a_quote_def = a_quote.this.definition

    Eq.a_quote_exp = Eq[-1].subs(Eq.a_quote_def.reversed)

    z = Symbol(Eq[1].lhs)
    Eq.z_def = z.this.definition

    Eq << Eq.z_def.subs(Eq.ksi_def.reversed, Eq.a_quote_def.reversed)

    Eq << Eq[-1][i]

    Eq << Eq[-1].this.rhs.apply(keras.softmax.to.mul.reducedSum)

    Eq.zi_def = Eq[-1].this.rhs.subs(Eq.a_quote_exp[i])

    Eq << Eq.ksi_def[i].this.find(BandPart).defun()

    Eq.ksi_def = Eq[-1].this.rhs.expr.apply(algebra.bool.to.piece)

    Eq << Eq.zi_def.find(ReducedSum).this.subs(Eq.ksi_def)

    Eq << Eq[-1].this.rhs.apply(algebra.reducedSum.to.sum)

    Eq << Eq[-1].this.find(Element).apply(sets.el.add, i)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.reducedSum)

    Eq << Eq[-1].this.find(Max).apply(keras.max.to.relu)

    Eq << Eq[-1].this(i).find(Min).simplify()

    Eq << Eq.zi_def.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Indexed).defun()

    Eq << Eq[-1].this.find(BandPart).defun()

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    j = Eq.ksi_def.rhs.variable
    Eq << Eq[-1][j]

    Eq << Eq[-1].this.find(Mul).apply(algebra.mul.to.piece)

    Eq.zij_def = Eq[-1].this.find(Element).apply(sets.el.negate)

    z_dquote = Symbol('z^\"', Eq[1].rhs)
    Eq.z_dquote_def = z_dquote.this.definition

    Eq.zi_dquote_def = Eq.z_dquote_def[i]

    Eq << Eq.zi_dquote_def[j]

    Eq << Eq[-1].this.find(ExprCondPair[2]).expr.apply(algebra.piece.swap, i=0)

    Eq << Eq[-1].this.find(And).apply(sets.et.to.el.range)

    Eq << Eq[-1].this.find(Element).apply(sets.el.sub, i)

    Eq << Eq[-1].this.find(Element).apply(sets.el.negate)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.flatten)

    Eq.zij_dquote_def = Eq[-1].this.rhs.apply(algebra.piece.swap, 1)

    Eq.zi_quote_def = Eq[0][i]

    Eq << Eq.zi_quote_def[j + Min(l, n) - i - 1]

    Eq << Eq.zij_dquote_def.this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this(j).find(Symbol < 0).simplify()

    Eq << Eq[-1].this.find(And).apply(algebra.et.collect, cond=Eq[-1].find(Element))

    Eq << Eq[-1].this.find(Element).apply(sets.el.negate)

    Eq << Eq[-1].this.find(Symbol < Symbol + 1).apply(algebra.lt.to.le.strengthen)

    Eq << Eq[-1].this.find(Symbol < Symbol + 1).apply(algebra.lt.to.le.strengthen)

    Eq << Eq[-1].this(i, j).find(And).apply(sets.et_ou.to.el_range.bandPart.lower.offset.st.le)

    Eq << Eq[-1].this.find(Element).apply(sets.el.negate)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.zij_def, Eq[-1])

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (j, 0, n), (i, 0, n))

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.z_dquote_def, Eq[-1])

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.z_def, Eq[-1])





if __name__ == '__main__':
    run()
# created on 2021-12-29
# updated on 2022-03-29
