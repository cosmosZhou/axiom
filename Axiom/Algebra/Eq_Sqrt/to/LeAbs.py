from util import *


@apply
def apply(eq_C):
    (C, S[C]), C_quote = eq_C.of(Equal[Mul[Transpose[OneMatrix * ReducedSum[Expr ** 2] ** (1 / 2)] ** -1]])
    return abs(C_quote @ C_quote.T) <= 1


@prove
def prove(Eq):
    from Axiom import Algebra, Discrete

    n, d = Symbol(domain=Range(2, oo))
    C, C_quote = Symbol(shape=(n, d), real=True)
    Eq << apply(Equal(C_quote, C / (sqrt(ReducedSum(C * C) * OneMatrix(d, n))).T))

    Eq << Algebra.LeAbs.of.And.apply(Eq[1])

    Eq <<= Algebra.Le.of.All.Le.apply(Eq[-2]), Algebra.Ge.of.All.Ge.apply(Eq[-1])

    i = Eq[-1].find(Indexed).index
    Eq <<= Algebra.Le.of.All.Le.apply(Eq[-2]), Algebra.Ge.of.All.Ge.apply(Eq[-1])

    j = Eq[-1].find(Indexed[2]).index
    Eq <<= Eq[-2].subs(Eq[0]), Eq[-1].subs(Eq[0])

    Eq <<= Eq[-2].this.find(MatMul).apply(Discrete.Dot.eq.ReducedSum), Eq[-1].this.find(MatMul).apply(Discrete.Dot.eq.ReducedSum)

    Eq << Eq[0][i]

    Eq << Algebra.Cond.to.Cond.domain_defined.apply(Eq[-1])

    Eq << Algebra.Ne_0.to.Gt_0.apply(Eq[-1])

    Eq << Eq[-1].subs(i, j)

    Eq <<= Algebra.Gt_0.Gt_0.to.Le_1.apply(Eq[-1], Eq[-2]), Algebra.Gt_0.to.Gt_0.Sqrt.apply(Eq[-1]) * Algebra.Gt_0.to.Gt_0.Sqrt.apply(Eq[-2])

    Eq << Algebra.Gt_0.Le.to.Le.Mul.apply(Eq[-1], Eq[-2])

    Eq << Algebra.LeAbs.to.And.apply(Eq[-1])

    Eq << Algebra.Gt_0.Le.to.Le.Div.apply(Eq[-4], Eq[-2])

    Eq << Algebra.Gt_0.Ge.to.Ge.Div.apply(Eq[-4], Eq[-1])





if __name__ == '__main__':
    run()
# created on 2022-04-02
# updated on 2023-06-25
