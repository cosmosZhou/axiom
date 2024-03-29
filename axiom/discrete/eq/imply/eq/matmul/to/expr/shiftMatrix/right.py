from util import *


@apply
def apply(eq, x):
    (i, j), wij = eq.of(Equal[ShiftMatrix])
    n, = x.shape
    return Equal(x @ wij @ wij.T, x)


@prove
def prove(Eq):
    from axiom import discrete, algebra, sets

    n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n,), real=True)
    w = Symbol(shape=(n, n, n, n), real=True)
    i, j = Symbol(domain=Range(n))
    Eq << apply(Equal(w[i, j], ShiftMatrix(n, i, j)), x)

    i, j = Eq[0].lhs.indices
    w = Eq[0].lhs.base
    Eq << (x @ w[i, j]).this.subs(Eq[0])

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs().find(Element).simplify()

    Eq << Eq[-1].this.rhs().find(Element[Symbol, Range[0]]).simplify()

    Eq << Eq[-1].this.rhs.expr.args[1].expr.apply(algebra.add.to.piece)

    Eq << Eq[-1].this.rhs().expr.args[1]().expr.simplify(wrt=Eq[-1].rhs.variable)

    Eq << Eq[-1].this.rhs.find(Piecewise, Piecewise).apply(algebra.piece.swap, 1)

    Eq << Eq[-1].this.rhs.find(Piecewise, Piecewise).apply(algebra.piece.swap, 0)

    Eq << Eq[-1].this.rhs.find(Piecewise, Piecewise).apply(algebra.piece.swap, 1)

    #\.et\w*\.(to|given)
    Eq << Eq[-1].this.rhs.find(Piecewise, Piecewise).find(And).apply(sets.ne.notin.to.notin)

    Eq << Eq[-1].this.rhs().expr.args[1].find(NotElement).apply(sets.notin.to.el.complement)

    Eq << Eq[-1].this.rhs().expr.args[1].find(NotElement).apply(sets.notin.to.el.complement)

    Eq << Eq[-1].this.rhs.find(Piecewise, Piecewise).apply(algebra.piece.et.invert, 0)

    

    Eq << (Eq[-1] @ w[i, j].T).this.rhs.subs(Eq[0])

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs().find(Element).simplify()

    Eq << Eq[-1].this.rhs.expr.args[-1].expr.apply(algebra.add.to.piece)

    Eq << Eq[-1].this.rhs.expr.args[1].expr.args[1].expr.apply(algebra.add.to.piece)

    Eq << Eq[-1].this.rhs.expr.args[1].expr.args[2].expr.apply(algebra.add.to.piece)

    Eq << Eq[-1].this.rhs().expr.args[1]().expr.simplify(wrt=Eq[-1].rhs.variable)

    Eq << Eq[-1].this.find(Piecewise, Piecewise).apply(algebra.piece.ou)

    Eq << Eq[-1].this.find(Piecewise, Piecewise).apply(algebra.piece.subs, reverse=True)

    Eq << Eq[-1].this.rhs().expr.args[1]().expr.simplify()

    
    


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-11-14
# updated on 2023-05-26
