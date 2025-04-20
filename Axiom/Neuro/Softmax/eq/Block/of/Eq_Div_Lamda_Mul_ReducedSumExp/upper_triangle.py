from util import *


@apply
def apply(eq):
    (((((A, i), (S[i], (S[i], u))), (S[i], S[0], (n,  S[u]))), (A[i + n - Min(n, u), i + n - Min(n, u):], (S[i], S[0], S[u]))), (A[i, i:Min(n, i + u)], (S[i], S[0], S[n]))), z = \
    eq.of(Equal[
        BlockMatrix[
            Lamda[
                Exp[Sliced[Indexed, Tuple[Add]]],
                Tuple[Expr - Expr]],
            Lamda[
                BlockMatrix[
                    Exp,
                    ZeroMatrix
                ],
            ]
        ] / Lamda[OneMatrix * ReducedSum[Exp]]])

    assert n >= 2 and u >= 2 and u <= n

    return Equal(softmax(A + (BandPart[0, u - 1](OneMatrix(n, n)) - 1) * oo), BlockMatrix(
        Lamda[i:n - u](BlockMatrix(ZeroMatrix(i), z[i], ZeroMatrix(n - i - u))),
        Lamda[i:u](BlockMatrix(ZeroMatrix(n - u + i), z[i + n - u, :u - i]))))


@prove
def prove(Eq):
    from Axiom import Neuro, Algebra, Set, Logic

    n = Symbol(domain=Range(2, oo))
    u = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    i = Symbol(integer=True)
    z = Symbol(shape=(n, u), real=True)
    Eq << apply(Equal(z, BlockMatrix(
        Lamda[i:n - u](Exp(A[i, i:i + u])),
        Lamda[i:u](BlockMatrix(Exp(A[i + n - u, n - u + i:]), ZeroMatrix(i)))) / Lamda[i:n](OneMatrix(u) * ReducedSum(Exp(A[i, i:Min(n, i + u)])))))

    i = Eq[1].find(Lamda).variable
    Ξ = Symbol(Eq[1].find(BandPart))
    Eq.ksi_def = Ξ.this.definition

    Eq << Algebra.Mul.eq.Exp.Infty.apply(exp(A) * Ξ).reversed

    a_quote = Symbol(Eq[-1].lhs.arg)
    Eq.a_quote_def = a_quote.this.definition

    Eq.a_quote_exp = Eq[-1].subs(Eq.a_quote_def.reversed)

    z = Symbol(Eq[1].lhs)
    Eq.z_def = z.this.definition

    Eq << Eq.z_def.subs(Eq.ksi_def.reversed, Eq.a_quote_def.reversed)

    Eq << Eq[-1][i]

    Eq << Eq[-1].this.rhs.apply(Neuro.Softmax.eq.Mul.ReducedSum)

    Eq.zi_def = Eq[-1].this.rhs.subs(Eq.a_quote_exp[i])

    Eq << Eq.ksi_def[i].this.find(BandPart).defun()

    Eq.ksi_def = Eq[-1].this.rhs.expr.apply(Logic.Bool.eq.Ite)

    Eq << Eq.zi_def.find(ReducedSum).this.subs(Eq.ksi_def)

    Eq << Eq[-1].this.rhs.apply(Algebra.ReducedSum.eq.Sum)

    Eq << Eq[-1].this.find(Element).apply(Set.Mem_Icc.Is.MemAdd, i)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.ReducedSum)

    Eq << Eq[-1].this(i).find(Max).simplify()

    Eq << Eq.zi_def.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Indexed).defun()

    Eq << Eq[-1].this.find(BandPart).defun()

    Eq << Eq[-1].this.find(Bool).apply(Logic.Bool.eq.Ite)

    j = Eq.ksi_def.rhs.variable
    Eq << Eq[-1][j]

    Eq.zij_def = Eq[-1].this.find(Mul).apply(Algebra.Mul.eq.Ite)

    z_dquote = Symbol('z^\"', Eq[1].rhs)
    Eq.z_dquote_def = z_dquote.this.definition

    Eq.zi_dquote_def = Eq.z_dquote_def[i]

    Eq << Eq.zi_dquote_def[j]

    Eq << Eq[-1].this.find(ExprCondPair).expr.apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite, i=0)

    Eq << Eq[-1].this.find(And).apply(Set.Cond.Cond.Is.Mem.Range, simplify=None)

    Eq << Eq[-1].this.find(Element).apply(Set.Mem_Icc.Is.MemSub, i, simplify=None)

    Eq << Eq[-1].this.rhs.apply(Logic.Ite_Ite.eq.Ite__Ite)

    Eq.zij_dquote_def = Eq[-1].this.rhs.apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite, 1)

    Eq.zi_quote_def = Eq[0][i]

    Eq << Eq.zi_quote_def[j - i]

    Eq << Eq.zij_dquote_def.this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this(j).find(Symbol < Symbol).simplify()

    Eq << Eq[-1].this.find(And).apply(Algebra.And.collect, cond=Eq[-1].find(Element))

    Eq << Eq[-1].this(i, j).find(And).apply(Set.Or.Or.Is.Mem.Range.BandPart.upper)

    Eq << Algebra.Eq.of.Eq.Eq.apply(Eq.zij_def, Eq[-1])

    Eq << Algebra.EqLamda.of.Eq.apply(Eq[-1], (j, 0, n), (i, 0, n))

    Eq << Algebra.Eq.of.Eq.Eq.apply(Eq.z_dquote_def, Eq[-1])

    Eq << Algebra.Eq.of.Eq.Eq.apply(Eq.z_def, Eq[-1])





if __name__ == '__main__':
    run()
# created on 2022-01-02

# updated on 2022-03-30
