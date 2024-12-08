from util import *


@apply
def apply(given):
    (((w, i, j), x), s), (S[x], S[s]) = given.of(All[Element[MatMul[Indexed]]])

    n = s.etype.shape[0]

    k = Symbol(integer=True)

    assert w[i, j].is_SwapMatrix or w[i, j].definition.is_SwapMatrix

    p = Symbol(shape=(oo,), integer=True, nonnegative=True)

    P = Symbol(conditionset(p[:n], Equal(p[:n].cup_finiteset(), Range(n))))

    return All[p[:n]:P, x:s](Element(Lamda[k:n](x[p[k]]), s))


@prove
def prove(Eq):
    from Axiom import Discrete, Algebra

    n = Symbol(domain=Range(2, oo))
    S = Symbol(etype=dtype.integer[n], given=True)
    x = Symbol(shape=(oo,), integer=True)
    i, j = Symbol(integer=True)
    w = Symbol(Lamda[j, i](SwapMatrix(n, i, j)))
    Eq.swap, (Eq.P_definition, Eq.w_definition), Eq.axiom = apply(All[x[:n]:S](Element(w[i, j] @ x[:n], S)))

    Eq << Discrete.All_Any_Eq_Dot_MatProd_SwapMatrix.factorization.apply(n)

    * _, b_i = Eq[-1].rhs.args[1].expr.args
    b, _i = b_i.args
    Eq << Eq.w_definition.subs(j, b[_i])

    Eq << Eq[-2].subs(Eq[-1].reversed)

    k = Eq.axiom.lhs.variable
    Eq << Eq[-1][k]

    Eq << Eq[-1].this.expr.expr.rhs.args[0].limits_subs(_i, k)

    Eq << Discrete.Lamda.eq.Dot.swapn.helper.apply(x[:n], b[:n], w)

    Eq << Algebra.All_Any_Eq.Cond.to.All.Any.subs.apply(Eq[-2].reversed, Eq[-1])

    Eq << Algebra.All.to.All.limits.restrict.apply(Eq[-1], (x[:n], S))

    Eq <<= Eq[-1] & Eq.axiom

    Eq << Eq[-1].this.expr.apply(Algebra.Cond.Any.of.Any.And, simplify=None)

    Eq << Eq[-1].this.expr.expr.apply(Algebra.Eq.Cond.of.And.subs)

    Eq << Eq[-1].this.expr.apply(Algebra.Any_And.of.And, index=-1)

    Eq << Algebra.All_And.of.And.All.apply(Eq[-1])

    Eq << Discrete.All_In.to.All_In.swapn.MatProd.apply(Eq.swap.T, n, b)




if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-09-03
# updated on 2023-08-26
