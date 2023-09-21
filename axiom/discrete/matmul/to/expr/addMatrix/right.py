from util import *


@apply
def apply(x, lamda, w=None):
    n = x.shape[0]
    i, j = Symbol(domain=Range(n))

    if w is None:
        w = Symbol(Lamda[j, i](AddMatrix(n, i, j, lamda)))
        w_quote = Symbol(Lamda[j, i](AddMatrix(n, i, j, -lamda)))
    else:
        assert w[i, j] == AddMatrix(n, i, j, lamda)
        assert w_quote[i, j] == AddMatrix(n, i, j, -lamda)

    return Equal(x @ w[i, j] @ w_quote[i, j], x)


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n,), real=True)
    lamda = Symbol(real=True)
    Eq << apply(x, lamda)

    i, j = Eq[0].lhs.indices
    w = Eq[0].lhs.base
    w_quote = Eq[1].lhs.base
    Eq << (x @ w[i, j]).this.subs(Eq[0])

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.find(Lamda)().find(Element[Range]).simplify()

    Eq << Eq[-1].this.find(Lamda)().find(Element[Complement]).simplify()

    Eq << Eq[-1].this.find(Piecewise).apply(algebra.piece.to.delta)

    Eq << Eq[-1].this.find(Piecewise).apply(algebra.piece.to.delta)

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.lamda)

    Eq << Eq[-1].this.rhs.simplify()

    Eq << (Eq[-1] @ w_quote[i, j]).this.rhs.subs(Eq[1])

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.find(Lamda)().find(Element[Range]).simplify()

    Eq << Eq[-1].this.find(Lamda)().find(Element[Complement]).simplify()

    Eq << Eq[-1].this.find(Piecewise).apply(algebra.piece.to.delta)

    Eq << Eq[-1].this.find(Piecewise).apply(algebra.piece.to.delta)

    Eq << Eq[-1].this.find(Mul[Add]).expand()

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.lamda)

    Eq << Eq[-1].this.find(Add[Mul]).apply(algebra.add.collect, factor=KroneckerDelta(i, j))

    Eq << Eq[-1].this.find(Mul).apply(algebra.mul.delta.to.zero)





if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-11-12
# updated on 2022-10-05
