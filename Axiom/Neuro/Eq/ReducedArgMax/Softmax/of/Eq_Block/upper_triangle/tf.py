from util import *


@apply
def apply(eq):
    (((((A, i), (S[i], (S[i], (n, u)))), (S[i], S[0], (S[1], S[n],  S[-Min(n, u)]))), (((S[A], S[i + n - Min(n, u) + 1]), (S[i + n - Min(n, u) + 1], S[n])), (S[i], S[0], (n, u)))), (S[A[i][i:Min(n, i + u)]], (S[i], S[0], S[n]))), z = \
    eq.of(Equal[
        BlockMatrix[
            Lamda[Sliced[Indexed, Tuple[Add[Min]]], Tuple[Add]],
            Lamda[
                BlockMatrix[
                    Sliced[Indexed],
                    NegativeInfinity * OneMatrix],
                Tuple[Min - 1]]] - Lamda[OneMatrix * logsumexp]])

    assert n >= 2 and u >= 2
    return Equal(ReducedArgMax(softmax(A + (BandPart[0, u - 1](OneMatrix(n, n)) - 1) * oo)) - Lamda[i:n](i), ReducedArgMax(z))


@prove
def prove(Eq):
    from Axiom import Neuro, Algebra

    n, u = Symbol(domain=Range(2, oo))
    A = Symbol(shape=(n, n), real=True)
    i = Symbol(integer=True)
    z = Symbol(shape=(n, Min(u, n)), extended_real=True)
    Eq << apply(Equal(z, BlockMatrix(
            Lamda[i:n - Min(u, n) + 1](A[i, i:i + Min(u, n)]),
            Lamda[i:Min(u, n) - 1](BlockMatrix(A[i + n - Min(u, n) + 1, n - Min(u, n) + i + 1:], -oo * OneMatrix(i + 1)))) - Lamda[i:n](OneMatrix(Min(u, n)) * logsumexp(A[i, i:Min(n, i + u)]))))

    Eq << Neuro.Softmax.eq.Block.of.Eq_Sub_Lamda_Mul_LogSumExp.upper_triangle.tf.apply(Eq[0])

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
        Lamda[i:Min(u, n) - 1](z[i + n + 1 - Min(n, u)]),
        Lamda[i:Min(u, n) - 1](BlockMatrix(z[i + n + 1 - Min(n, u), :Min(u, n) - i - 1], -oo * OneMatrix(i + 1))),
        plausible=True)

    i_ = Symbol("i", domain=Range(Min(u, n) - 1))
    Eq << Algebra.Eq.given.Eq.getitem.apply(Eq.eq_lamda, i_)

    j_ = Symbol("j", domain=Range(Min(u, n)))
    Eq << Algebra.Eq.given.Eq.getitem.apply(Eq[-1], j_)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].this.apply(Algebra.Eq.transport, 0)

    j = Symbol(integer=True)
    Eq << Eq[0][i + n + 1 - Min(n, u), j - i]

    Eq << Algebra.EqLamda.of.Eq.apply(Eq[-1], (j, i, Min(u, n) - 1))

    Eq.zi_min_def = Eq[-1].this(i).find(Lamda)(j).find(Add < Min - 1).simplify()

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
# updated on 2023-05-18
