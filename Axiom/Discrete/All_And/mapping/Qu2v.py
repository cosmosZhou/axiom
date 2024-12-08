from util import *


@apply
def apply(n, u, v):
    Q, w, x = predefined_symbols(n)
    X, index = X_definition(n, w, x)
    return All[x[:n + 1]:Q[u]](Element(X[v], Q[v]) & Equal(x[:n + 1], w[n, index[u](X[v])] @ X[v]))


def X_definition(n, w, x):
    from Axiom.Discrete.Eq.to.And.index import index_function
    j = Symbol(integer=True)

    index = index_function(n + 1)
    return Symbol('X', Lamda[j:n + 1](w[n, index[j](x[:n + 1], evaluate=False)] @ x[:n + 1])), index


def predefined_symbols(n):
    x = Symbol(shape=(oo,), integer=True, nonnegative=True)
    t, i, j = Symbol(integer=True)
    Q = Symbol(Lamda[t:n + 1](conditionset(x[:n + 1], Equal(x[:n + 1].cup_finiteset(), Range(n + 1)) & Equal(x[n], t))))
    w = Symbol(Lamda[j, i](SwapMatrix(n + 1, i, j)))

    return Q, w, x


@prove(proved=False)
def prove(Eq):
    from Axiom import Sets, Algebra, Discrete

    n = Symbol(integer=True, positive=True, given=True)
    u = Symbol(domain=Range(n + 1), given=True)
    v = Symbol(domain=Range(n + 1))
    Eq << apply(n, u, v)

    w, i, j = Eq[0].lhs.args
    Q = Eq[2].lhs.base
    Eq << Sets.All_Eq_.CupFiniteSet.Range.apply(Q[u])

    Eq.x_slice_last, Eq.x_slice_domain = Algebra.All_And.to.And.All.apply(Eq[-1])

    Eq << Eq.x_slice_domain.this.expr.apply(Discrete.Eq.to.And.index, v)

    Eq.h_domain, Eq.x_h_equality = Algebra.All_And.to.And.All.apply(Eq[-1])

    hv = Eq.x_h_equality.expr.lhs.indices[0]
    Eq << Discrete.All_InDot.permutation.apply(n + 1, w=w)

    Eq << Subset(Eq[-2].limits[0][1], Eq[-1].rhs, plausible=True)

    Eq << Sets.Subset.All.to.All.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].subs(Eq[-1].rhs.this.definition)

    Eq << Eq[-1].this.expr.simplify()

    Eq << Eq[-1].subs(i, n)

    Eq << Eq[-1].subs(j, hv)

    k = Eq[-1].expr.lhs.expr.arg.args[0].indices[-1]
    Eq.Xv_definition = Eq[1].subs(j, v)

    Eq << Eq.Xv_definition[k].apply(Sets.Eq.to.Eq.Cup.FiniteSet, (k, 0, n + 1))

    Eq.x_n1_cup_finiteset = Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq.Xv_definition[n]

    Eq << Eq[0].subs(i, n).subs(j, hv)[n]

    Eq << Eq[-2].this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.expand()

    Eq << Algebra.All_Eq.Cond.to.All.subs.apply(Eq.x_h_equality, Eq[-1])

    return
    Eq << Eq[-1].this.expr.apply(Algebra.eq_piecewise.then.ou)
    Eq << Algebra.All_And.then.all.apply(Eq[-1] & Eq.h_domain)
    return
    Eq <<= Eq.x_n1_cup_finiteset & Eq[-1]
    Eq.Xv_in_Qv, Eq.x_eq_swap_Xv = Algebra.All_And.of.all.apply(Eq[3])
    Eq << Eq.Xv_in_Qv.this.expr.rhs.definition
    Eq.indexu_eq_indexu = Eq.x_eq_swap_Xv.function.rhs.args[0].indices[1].this.subs(Eq.Xv_definition)
    Eq.indexu_eq_indexv = Eq.x_slice_domain.this.expr.apply(Discrete.combinatorics.permutation.index.swap, u, v, w=w)
    Eq << Eq.x_slice_domain.this.expr.apply(Discrete.Eq.to.And.index, u)
    Eq.indexu_contains, Eq.x_indexu_equality = Algebra.All_And.then.all.apply(Eq[-1], simplify=None)
    Eq.equality_of_indexu_and_n = (Eq.x_indexu_equality & Eq.x_slice_last).this.expr.apply(Algebra.Eq.Eq.then.eq.transit)
    i, j, m = Symbol(domain=Range(n + 1))
    Eq << Eq.x_slice_domain.this.expr.apply(Discrete.combinatorics.permutation.index.kronecker_delta.indexOf, i, j)
    x = Eq[-1].variable.base
    Eq.ou = Eq[-1].subs(i, x[n])
    Eq << Any(Eq.ou.function.args[0], *Eq.ou.limits, plausible=True)
    Eq << Algebra.All.any.then.Any_And.apply(Eq.x_slice_last, Eq[-1])
    Eq <<= Eq.ou & ~Eq[-1]
    Eq << Algebra.All_And.then.all.apply(Eq[-1], index=1)
    Eq.indexOf_indexed = Eq.x_slice_domain.this.expr.apply(Discrete.combinatorics.permutation.index.indexOf_indexed, j=m)
    Eq << Eq.indexOf_indexed.subs(m, n)
    Eq << (Eq[-2] & Eq[-1]).this.expr.apply(Algebra.Eq.Eq.then.eq.subs)
    Eq.ou = Eq[-1].subs(j, Eq.equality_of_indexu_and_n.function.lhs)
    Eq << Any(Eq.ou.function.args[0], *Eq.ou.limits, plausible=True)
    Eq << Algebra.All.any.then.Any_And.apply(Eq.x_indexu_equality, Eq[-1])
    Eq <<= Eq.ou & ~Eq[-1]
    Eq << Algebra.All_And.then.all.apply(Eq[-1], index=1)
    Eq.ou = Eq.indexOf_indexed.subs(m, Eq.equality_of_indexu_and_n.function.lhs.indices[0])
    Eq << Any(Eq.ou.function.args[0], *Eq.ou.limits, plausible=True)
    Eq <<= Eq.indexu_contains & Eq[-1]
    Eq.index_equality = Algebra.All_And.then.all.apply(Eq.ou & ~Eq[-1], index=1)
    Eq << Discrete.combinatorics.permutation.is_nonempty.Qu.apply(n, u)
    Eq <<= Eq[-3] & Eq.index_equality
    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Eq.then.eq.subs)
    Eq <<= Eq[-1] & Eq.equality_of_indexu_and_n
    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Eq.then.eq.subs)
    Eq <<= Eq.indexu_eq_indexv & Eq[-1]
    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Eq.then.eq.subs, swap=True, reverse=True)
    Eq << Algebra.All_Eq.Cond.to.All.subs.apply(Eq[-1], Eq.indexu_eq_indexu)
    Eq <<= Eq.x_eq_swap_Xv & Eq[-1]
    Eq << Eq[-1].this.expr.apply(Algebra.et.of.et.subs.eq, index=0)
    Eq << Algebra.All_And.of.all.apply(Eq[-1])
    Eq << Eq[-1].subs(Eq.Xv_definition)
    Eq << Discrete.matrix.elementary.swap.multiply.left.apply(x[:n + 1], i=n, j=Eq.h_domain.lhs, w=w)
    Eq << Eq[-2].subs(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-07-26
