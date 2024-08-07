from util import *


@apply
def apply(eq):
    (w, i, j), (S[i], S[j]) = eq.of(Equal[Indexed, SwapMatrix])
    return Equal(w[i, j], w[j, i])


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol(domain=Range(2, oo))
    i, j = Symbol(domain=Range(n))
    w = Symbol(real=True, shape=(n, n, n, n))
    Eq << apply(Equal(w[i, j], SwapMatrix(n, i, j)))

    t = Symbol(domain=Range(n))
    Eq << Eq[0].subs(i, t).subs(j, i).subs(t, j)

    Eq << Eq[0] @ Eq[-1]

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.find(ExprCondPair[3])().find(KroneckerDelta * KroneckerDelta).simplify()

    Eq << Eq[-1].this.find(ExprCondPair[3])().find(KroneckerDelta * KroneckerDelta).simplify()

    Eq << Eq[-1].this.rhs.expr.args[-1].expr.args[0].apply(algebra.add.to.piece)

    Eq << Eq[-1].this.rhs().find(Element).simplify()

    Eq << Eq[-1].this.rhs.expr.apply(algebra.piece.to.delta)

    Eq << Eq[-1].this.rhs.apply(algebra.lamda.to.identity)

    Eq << discrete.eq.imply.eq.matpow.to.identity.apply(Eq[0])

    Eq << Eq[-1].subs(Eq[-2].reversed)

    Eq << w[i, j].inverse() @ Eq[-1]







if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-08-25
# updated on 2023-05-21
