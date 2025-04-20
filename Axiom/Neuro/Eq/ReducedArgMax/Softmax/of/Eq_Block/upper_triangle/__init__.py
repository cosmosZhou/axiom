from util import *


@apply
def apply(eq):
    (((((A, i), (S[i], (S[i], u))), (S[i], S[0], (n,  S[u]))), (((S[A], S[i + n - u]), (S[i + n - u], S[n])), (S[i], S[0], S[u]))), (A[i, i:Min(n, i + u)], (S[i], S[0], S[n]))), z = \
    eq.of(Equal[
        BlockMatrix[
            Lamda[
                Sliced[Indexed, Tuple[Add]],
                Tuple[Expr - Expr]
            ],
            Lamda[
                BlockMatrix[
                    Sliced[Indexed],
                    NegativeInfinity * OneMatrix],
            ]
        ] - Lamda[OneMatrix * logsumexp]])

    assert n >= 2 and u >= 2 and u <= n
    return Equal(ReducedArgMax(softmax(A + (BandPart[0, u - 1](OneMatrix(n, n)) - 1) * oo)) - Lamda[i:n](i), ReducedArgMax(z))


@prove
def prove(Eq):
    from Axiom import Neuro, Algebra

    n = Symbol(domain=Range(2, oo))
    u = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    i = Symbol(integer=True)
    z = Symbol(shape=(n, u), extended_real=True)
    Eq << apply(Equal(z, BlockMatrix(
            Lamda[i:n - u](A[i, i:i + u]),
            Lamda[i:u](BlockMatrix(A[i + n - u, n - u + i:], -oo * OneMatrix(i)))) - Lamda[i:n](OneMatrix(u) * logsumexp(A[i, i:Min(n, i + u)]))))

    Eq << Neuro.Softmax.eq.Block.of.Eq_SubBlock__Lamda_Mul_LogSumExp.upper_triangle.apply(Eq[0])

    z_quote = Symbol(Eq[-1].lhs)
    Eq << Eq[-1].subs(z_quote.this.definition.reversed)

    Eq << Algebra.EqReducedArgMax.of.Eq.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.ReducedArgMax.eq.Block.ReducedArgMax)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax).apply(Algebra.ReducedArgMax.eq.Lamda.ReducedArgMax)

    Eq << Eq[-1].this.find(ReducedArgMax[Lamda]).apply(Algebra.ReducedArgMax.eq.Lamda.ReducedArgMax)

    Eq << Eq[-1].this.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.Add)

    Eq << Eq[-1].this.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.ReducedArgMax)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax[Exp]).apply(Algebra.ReducedArgMax.Exp.eq.ReducedArgMax)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.Add)

    Eq << Eq[-1].this.find(ReducedArgMax[Exp]).apply(Algebra.ReducedArgMax.Exp.eq.ReducedArgMax)

    Eq << Eq[-1].this.find(BlockMatrix).apply(Algebra.Block.eq.Lamda.Ite)

    Eq << Eq[-1].this.find(Piecewise).apply(Algebra.Ite.eq.Add)

    Eq << Eq[-1].this.find(Lamda).apply(Algebra.Lamda.eq.Add)

    Eq.eq_reducedArgMax = Eq[-1].this.find(Lamda[Piecewise]).apply(Algebra.Lamda.Ite.eq.Block)

    Eq.eq_lamda = Equal(
        Lamda[i:Min(u, n)](z[i + n - Min(n, u)]),
        Lamda[i:Min(u, n)](BlockMatrix(z[i + n - Min(n, u), :Min(u, n) - i], -oo * OneMatrix(i))),
        plausible=True)

    i_ = Symbol("i", domain=Range(Min(u, n)))
    Eq << Algebra.Eq.given.Eq.getitem.apply(Eq.eq_lamda, i_)

    j_ = Symbol("j", domain=Range(Min(u, n)))
    Eq << Algebra.Eq.given.Eq.getitem.apply(Eq[-1], j_)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].this.apply(Algebra.Eq.transport, lhs=0)

    j = Symbol(integer=True)
    Eq << Eq[0][i + n - Min(n, u), j - i]

    Eq << Algebra.EqLamda.of.Eq.apply(Eq[-1], (j, i, Min(u, n)))

    Eq.zi_min_def = Eq[-1].this(i).find(Lamda)(j).find(Add < Symbol).simplify()

    Eq << Eq.eq_lamda.subs(Eq.zi_min_def)

    Eq << Algebra.EqReducedArgMax.of.Eq.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.ReducedArgMax.eq.Lamda.ReducedArgMax)

    Eq << Eq[-1].this.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.ReducedArgMax)

    Eq << Eq[-1].subs(Eq.zi_min_def.reversed)

    Eq << Eq[-1].this.lhs.apply(Algebra.ReducedArgMax.eq.Lamda.ReducedArgMax, simplify=None).reversed

    Eq << Eq.eq_reducedArgMax.subs(Eq[-1])

    Eq << Eq[-1].this.find(BlockMatrix).apply(Algebra.Block.eq.Lamda.Ite)

    Eq << Eq[-1].this.apply(Algebra.Eq.transport, rhs=0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Lamda.eq.ReducedArgMax)

    Eq << Eq[-1].this.lhs.find(ReducedArgMax).arg.definition





if __name__ == '__main__':
    run()
# created on 2022-01-03
# updated on 2023-05-20

from . import tf
