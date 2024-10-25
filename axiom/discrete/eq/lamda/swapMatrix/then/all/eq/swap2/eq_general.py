from util import *


@apply
def apply(eq_w):
    (w, i, j), (S[i], S[j]) = eq_w.of(Equal[Indexed, SwapMatrix])
    n = w.shape[-1]
    domain = Range(n)
    t = Symbol(domain=domain)
    assert n >= 2
    return All(Equal(w[t, i] @ w[t, j] @ w[t, i], w[i, j]), (j, domain - {i, t}))


@prove
def prove(Eq):
    from axiom import discrete, algebra, sets

    n = Symbol(domain=Range(2, oo))
    w = Symbol(integer=True, shape=(n, n, n, n))
    i, j = Symbol(domain=Range(n))
    Eq << apply(Equal(w[i, j], SwapMatrix(n, i, j)))

    t = Eq[1].expr.lhs.args[0].indices[0]
    p = Symbol(complex=True, zero=False)
    x = Lamda[i:n](p ** i)
    Eq << (w[t, i] @ x).this.subs(Eq[0].subs(i, t).subs(j, i))

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs().expr.simplify()

    Eq << (w[t, j] @ Eq[-1]).this.rhs.subs(Eq[0].subs(i, t))

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.expr.args[-1].expr.apply(algebra.add.to.piece)

    Eq << Eq[-1].this.rhs.expr.args[1].expr.apply(algebra.add.to.piece)

    Eq << Eq[-1].this.rhs().expr.simplify(wrt=True)

    Eq << Eq[-1].this.rhs.expr.args[-1].expr.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs().expr.apply(algebra.piece.swap, -2)

    Eq << Eq[-1].this.rhs().expr.args[2].cond.simplify()

    Eq << Eq[-1].this.rhs.expr.args[2].cond.apply(sets.el.to.ou.split.finiteset)

    Eq << Eq[-1].this.rhs().expr.apply(algebra.piece.et.invert, 1)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.piece.subs, index=2)

    Eq << algebra.cond.then.all.restrict.apply(Eq[-1], (j,))

    Eq << algebra.cond.then.all.restrict.apply(Eq[-1], Eq[1].limits[0])

    Eq << Eq[-1].this().expr.simplify()

    Eq << Eq[-1].this.expr.apply(discrete.eq.then.eq.rmatmul, w[t, i])

    Eq << Eq[-1].this.expr.rhs.subs(Eq[0].subs(i, t).subs(j, i))

    Eq << Eq[-1].this.expr.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this().expr.rhs().expr.simplify(wrt=True)

    Eq << Eq[-1].this().expr.rhs().expr.args[-1].expr.args[1].apply(algebra.piece.swap)

    Eq << Eq[-1].this.expr.rhs.expr.apply(algebra.piece.to.delta)

    Eq.www_expansion = Eq[-1].this().expr.rhs.expr.simplify()

    Eq << algebra.cond.then.all.domain_defined.apply(Eq[0], j)

    Eq << Eq[-1].simplify()

    j = j.unbounded
    Eq << (w[i, j] @ x).this.subs(Eq[-1]).this.rhs.apply(discrete.matmul.to.lamda)
    Eq << Eq[-1].this(j).rhs().expr.simplify(wrt=True)
    Eq << Eq[-1].this.rhs.expr.apply(algebra.piece.to.delta)
    Eq << Eq.www_expansion.subs(Eq[-1].reversed)
    Eq << Eq[-1].this.expr.apply(discrete.eq_matmul.then.eq.matrix.independence.st.rmatmul)




if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-08-23
# updated on 2023-05-21
