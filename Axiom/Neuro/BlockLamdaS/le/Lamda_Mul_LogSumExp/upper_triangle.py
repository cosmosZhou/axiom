from util import *


@apply
def apply(A, u):
    n, S[n] = A.shape
    assert A.is_real
    assert n >= 2 and u >= 2 and u <= n
    i = Symbol(integer=True)
    return BlockMatrix(
            Lamda[i:n - u](A[i, i:i + u]),
            Lamda[i:u](BlockMatrix(A[i + n - u, n - u + i:], -oo * OneMatrix(i)))) <= Lamda[i:n](OneMatrix(u) * logsumexp(A[i, i:Min(n, i + u)]))


@prove
def prove(Eq):
    from Axiom import Algebra, Neuro, Logic

    n = Symbol(domain=Range(2, oo))
    u = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    Eq << apply(A, u)

    Eq << Algebra.Le.given.All.Le.apply(Eq[0])

    Eq << Algebra.Le.given.Le_0.apply(Eq[-1])

    Eq << Logic.Cond_Ite__Ite.given.And.ou.OrAndS.apply(Eq[-1])

    Eq << Eq[-1].this.find(LessEqual).apply(Algebra.Le_0.given.Le)

    Eq << Eq[-1].this.find(LessEqual[ZeroMatrix]).apply(Algebra.Le_0.given.Le)

    Eq << Eq[-1].this.find(LessEqual[BlockMatrix]).apply(Algebra.LeBlock.given.And.Le)

    Eq.ou = Eq[-1].this.find(LessEqual[Mul, logsumexp]).apply(Algebra.Le.given.All.Le)

    Eq <<= Neuro.Le_LogSumExp.apply(Eq.ou.args[1].find(Sliced)), Neuro.Le_LogSumExp.apply(Eq.ou.find(Sliced))

    Eq <<= Eq.ou.find(Less).this.apply(Algebra.Lt.of.Lt.transport, rhs=1), Eq.ou.find(GreaterEqual).this.apply(Algebra.Ge.of.Ge.transport, rhs=1)

    Eq <<= Eq[-1].this.rhs.apply(Algebra.EqMin.of.Ge), Eq[-2].this.rhs.apply(Algebra.EqMin.of.Lt)

    Eq <<= Logic.Imp.And.of.Cond.Imp.rhs.apply(Eq[-2], Eq[-6]), Logic.Imp.And.of.Cond.Imp.rhs.apply(Eq[-1], Eq[-5])

    Eq <<= Eq[-2].this.rhs.apply(Logic.Cond.of.Eq.Cond.subs, reverse=True, index=1), Eq[-1].this.rhs.apply(Logic.Cond.of.Eq.Cond.subs, reverse=True, index=1)

    Eq << Logic.Or.of.Imp.Imp.apply(Eq[-2], Eq[-1])





if __name__ == '__main__':
    run()
# created on 2022-04-01
# updated on 2023-05-25
