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

    Eq << Algebra.All.Any.of.All_Any_Eq.Cond.subs.apply(Eq[-2].reversed, Eq[-1])

    Eq << Algebra.All.of.All.limits.restrict.apply(Eq[-1], (x[:n], S))

    Eq <<= Eq[-1] & Eq.axiom

    Eq << Eq[-1].this.expr.apply(Algebra.Cond.Any.given.Any.And, simplify=None)

    Eq << Eq[-1].this.expr.expr.apply(Algebra.Eq.Cond.given.And.subs)

    Eq << Eq[-1].this.expr.apply(Algebra.Any_And.given.And, index=-1)

    Eq << Algebra.All_And.given.And.All.apply(Eq[-1])

    Eq << Discrete.All_Mem.of.All_Mem.swapn.MatProd.apply(Eq.swap.T, n, b)




if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-09-03
# updated on 2023-08-26
