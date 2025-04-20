from util import *


@apply
def apply(eq):
    (H, ((((A, i), (S[i], (S[i], u))), (S[i], S[0], (n, S[u]))), (A[i + n - u, i + n - u:], (S[i], S[0], S[u]))), ((H[i], A[i, i:Min(n, i + u)]), (S[i], S[0], S[n]))), z = \
    eq.of(
        Equal[
            BlockMatrix[1][Expr, ZeroMatrix] + BlockMatrix[
                Lamda[Sliced[Indexed, Tuple[Add]], Tuple[Expr - Expr]],
                Lamda[BlockMatrix[NegativeInfinity * OneMatrix]]
            ] - Lamda[OneMatrix * logsumexp[Add[BlockMatrix[Expr, ZeroMatrix]]]]])
    assert n >= 2 and u >= 2 and u <= n

    return Equal(softmax(A + H * Identity(n) + (BandPart[0, u - 1](OneMatrix(n, n)) - 1) * oo),
                 BlockMatrix(
                     Lamda[i:n - u](BlockMatrix(ZeroMatrix(i), Exp(z[i]), ZeroMatrix(n - i - u))),
                     Lamda[i:u](BlockMatrix(ZeroMatrix(n - u + i), Exp(z[i + n - u, :u - i])))))


@prove
def prove(Eq):
    from Axiom import Algebra, Neuro, Logic

    n = Symbol(domain=Range(2, oo))
    u = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    H = Symbol(shape=(n,), real=True)
    z = Symbol(shape=(n, u), real=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(z, BlockMatrix[1](H, ZeroMatrix(n, u - 1)) + BlockMatrix(
            Lamda[i:n - u](A[i, i:i + u]),
            Lamda[i:u](BlockMatrix(A[i + n - u, n - u + i:], -oo * OneMatrix(i)))) - Lamda[i:n](OneMatrix(u) * logsumexp((A[i, i:Min(n, i + u)] + BlockMatrix(H[i], ZeroMatrix(Min(n - i, u) - 1)))))))

    Eq << Eq[0].this.find(BlockMatrix[1]).apply(Algebra.Block.split, n - Min(u, n))

    Eq << Add(*Eq[-1].find(Add[BlockMatrix]).args[:2]).this.apply(Algebra.Add.Block.eq.Block)

    Eq.z_def = Eq[-2].subs(Eq[-1])

    A = Symbol(Add(*Eq[1].lhs.arg.args[:2]))
    Eq.A_def = A.this.definition

    Eq << Eq.A_def[i + n - Min(u, n)][i + n - Min(u, n):]

    Eq << Eq[-1].this.find(Mul[Lamda]).apply(Algebra.Expr.eq.Lamda, simplify=None)

    Eq << Eq[-1].this.find(Lamda).apply(Algebra.Lamda.Delta.eq.Mul.Lamda)

    Eq << Eq[-1].this.find(Lamda).apply(Algebra.Lamda.Delta.eq.Block)

    Eq << Eq[-1].this.find(Mul[BlockMatrix]).apply(Algebra.Mul.eq.Block)

    Eq.matmul_subs = Eq[-1].this.apply(Algebra.Eq.transport, rhs=0).reversed

    Eq << Eq.z_def.rhs.find(Add[2]).this.args[0].apply(Algebra.Expr.eq.Lamda, i)

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.eq.Lamda)

    Eq << Eq[-1].this.rhs.subs(Eq.matmul_subs)

    Eq << Eq[-1].this.rhs.find(Add).apply(Algebra.Expr.eq.Lamda)

    Eq << Eq[-1].this.rhs.find(-Piecewise).apply(Algebra.Mul.eq.Ite)

    Eq << Eq[-1].this.rhs.find(Add).apply(Algebra.Add.Ite.eq.Ite)

    Eq << Eq[-1].this.find(Piecewise).apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite, 1)

    Eq << Eq[-1].this.rhs.find(Add[Piecewise]).apply(Algebra.Add.eq.Ite)

    Eq << Eq[-1].this.rhs.find(Add[Piecewise]).apply(Algebra.Add.eq.Ite)

    Eq << Eq[-1].this.rhs.find(Piecewise).apply(Logic.Ite_Ite.eq.Ite__Ite)

    Eq.lower_part = Eq[-1].this.rhs.apply(Algebra.Lamda.Ite.eq.Lamda.Block)

    Eq << Eq.A_def[i]#[i:i + Min(u, n)]

    Eq << Algebra.All.of.Cond.restrict.apply(Eq[-1], (i, 0, n - Min(u, n)))

    Eq << Algebra.All.Eq.Slice.of.All_Eq.apply(Eq[-1], slice(i, i + Min(u, n)))

    Eq << Eq[-1].this.find(KroneckerDelta).apply(Algebra.Delta.offset, -i)

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Expr.eq.Lamda, simplify=None)

    Eq << Eq[-1].this.find(Lamda).apply(Algebra.Lamda.Delta.eq.Mul.Lamda)

    Eq << Eq[-1].this.find(Lamda).apply(Algebra.Lamda.Delta.eq.Block)

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul.eq.Block)

    Eq << Algebra.EqLamda.of.All_Eq.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Lamda.eq.Add)

    Eq.upper_part = Eq[-1].this.find(Lamda[BlockMatrix]).apply(Algebra.Lamda.Block.eq.Block.Lamda)

    Eq << Eq.A_def[i][i:Min(n, i + u)]

    Eq << Eq[-1].this.find(KroneckerDelta).apply(Algebra.Delta.offset, -i)

    Eq << Eq[-1].this.find(Mul[Lamda]).apply(Algebra.Expr.eq.Lamda, simplify=None)

    Eq << Eq[-1].this.find(Lamda).apply(Algebra.Lamda.Delta.eq.Mul.Lamda)

    Eq << Eq[-1].this.find(Lamda).apply(Algebra.Lamda.Delta.eq.Block)

    Eq << Eq[-1].this.find(Mul[BlockMatrix]).apply(Algebra.Mul.eq.Block)

    Eq << Eq[-1].this.find(ZeroMatrix).shape[0].find(Min).apply(Algebra.Min.eq.Add, i)
    Eq << Eq.z_def.subs(Eq[-1].reversed, Eq.upper_part.reversed, Eq.lower_part)

    Eq << Neuro.Softmax.eq.Block.of.Eq_SubBlock__Lamda_Mul_LogSumExp.upper_triangle.apply(Eq[-1])

    Eq << Eq[-1].this.find(Symbol).definition





if __name__ == '__main__':
    run()
# created on 2022-03-13
# updated on 2023-09-17

