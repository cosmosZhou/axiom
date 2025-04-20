from util import *


@apply
def apply(eq):
    (((((A, i), (S[0], S[i + 1])), (S[i], S[0], l)), (A[i + l, i + 1:i + l + 1], (S[i], S[0], (n, S[l])))), (A[i, relu(i - l + 1):i + 1], (S[i], S[0], S[n]))), z = \
    eq.of(
        Equal[
            BlockMatrix[
                Lamda[
                    BlockMatrix[
                        NegativeInfinity * OneMatrix,
                        Sliced[Indexed]
                    ],
                ],
                Lamda[Tuple[Expr - Expr]]
                ] - Lamda[OneMatrix * logsumexp]
            ])

    assert n >= 2 and l >= 2 and l <= n
    return Equal(ReducedArgMax(softmax(A + (BandPart[l - 1, 0](OneMatrix(n, n)) - 1) * oo)) - Lamda[i:n](i), ReducedArgMax(z) - l + 1)


@prove
def prove(Eq):
    from Axiom import Neuro, Algebra, Logic

    n = Symbol(domain=Range(2, oo))
    l = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    i = Symbol(integer=True)
    z = Symbol(shape=(n, l), extended_real=True)
    Eq << apply(Equal(z, BlockMatrix(
            Lamda[i:l](BlockMatrix(-oo * OneMatrix(l - i - 1), A[i, :i + 1])),
            Lamda[i:n - l](A[i + l, i + 1:i + l + 1])) - Lamda[i:n](OneMatrix(l) * logsumexp(A[i, relu(i + 1 - l):i + 1]))))

    Eq << Neuro.Softmax.eq.Block.of.Eq_Sub_Lamda_Mul_LogSumExp.lower_triangle.apply(Eq[0])

    z_quote = Symbol(Eq[-1].lhs)
    Eq << Eq[-1].subs(z_quote.this.definition.reversed)

    Eq << Algebra.EqReducedArgMax.of.Eq.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.ReducedArgMax.eq.Block.ReducedArgMax)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax).apply(Algebra.ReducedArgMax.eq.Lamda.ReducedArgMax)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax[Lamda]).apply(Algebra.ReducedArgMax.eq.Lamda.ReducedArgMax)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.ReducedArgMax)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax[Exp]).apply(Algebra.ReducedArgMax.Exp.eq.ReducedArgMax)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.Add)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.ReducedArgMax)

    Eq.eq_reducedArgMax = Eq[-1].this.rhs.find(ReducedArgMax[Exp]).apply(Algebra.ReducedArgMax.Exp.eq.ReducedArgMax)

    Eq.eq_lamda = Equal(
        Lamda[i:Min(l, n)](z[i]),
        Lamda[i:Min(l, n)](BlockMatrix(-oo * OneMatrix(Min(l, n) - i - 1), z[i, Min(l, n) - i - 1:])),
        plausible=True)

    i_ = Symbol("i", domain=Range(Min(l, n)))
    Eq << Algebra.Eq.given.Eq.getitem.apply(Eq.eq_lamda, i_)

    j_ = Symbol("j", domain=Range(Min(l, n)))
    Eq << Algebra.Eq.given.Eq.getitem.apply(Eq[-1], j_)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].this.apply(Algebra.Eq.transport, lhs=0)

    Eq << Eq[-1].this.rhs.apply(Logic.Ite_Ite.eq.Ite__Ite)

    j = Symbol(integer=True)
    Eq << Eq[0][i, j + Min(l, n) - i - 1]

    Eq << Algebra.EqLamda.of.Eq.apply(Eq[-1], (j, 0, i + 1))

    Eq.zi_min_def = Eq[-1].this.find(Lamda)(j).find(Symbol < 0).simplify()

    Eq << Eq.eq_lamda.subs(Eq.zi_min_def)

    Eq << Algebra.EqReducedArgMax.of.Eq.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.ReducedArgMax.eq.Lamda.ReducedArgMax)

    Eq << Eq[-1].this.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.Add)

    Eq << Eq[-1].subs(Eq.zi_min_def.reversed)

    Eq << Eq[-1].this.lhs.apply(Algebra.ReducedArgMax.eq.Lamda.ReducedArgMax)

    Eq << Eq[-1].this.apply(Algebra.Eq.transport, rhs=slice(0, 2)).reversed

    Eq << Eq[-1].this.lhs.apply(Algebra.Lamda.eq.Add)

    Eq << Eq[-1].this.apply(Algebra.Eq.transport, lhs=-1)

    Eq << Eq.eq_reducedArgMax.subs(Eq[-1])

    Eq << Eq[-1].this.find(Lamda + Lamda).apply(Algebra.Add.eq.Lamda)

    Eq << Eq[-1].this.find(BlockMatrix).apply(Algebra.Block.eq.Lamda.Ite)

    Eq << Eq[-1].this.find(Lamda).apply(Algebra.Lamda.eq.Add)

    Eq << Eq[-1].this.find(Lamda[2]).apply(Algebra.Lamda.eq.ReducedArgMax)

    Eq << Eq[-1].this.apply(Algebra.Eq.transport, rhs=3)

    Eq << Eq[-1].this.find(ReducedArgMax).arg.definition





if __name__ == '__main__':
    run()
# created on 2022-01-03

# updated on 2023-05-20

from . import tf
