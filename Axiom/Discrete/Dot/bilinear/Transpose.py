from util import *


@apply
def apply(self):
    x, W, y = self.of(MatMul)
    return Equal(self, y @ W.T @ x)


@prove
def prove(Eq):
    from Axiom import Discrete, Algebra

    n = Symbol(integer=True)
    x, y = Symbol(shape=(n,), real=True)
    W = Symbol(shape=(n, n), real=True)
    Eq << apply(x @ W @ y)

    i, j = Symbol(domain=Range(n))
    Eq << (x @ W).this.apply(Discrete.Dot.eq.Lamda, var={i, j})

    Eq << Eq[-1] @ y

    Eq << Eq[-1].this.rhs.apply(Discrete.Dot.eq.Sum)

    Eq.expansion = Eq[-1].this.rhs.expr.apply(Algebra.Mul.eq.Sum)

    Eq << Eq.expansion.subs(W, W.T)

    Eq << Eq[-1].apply(Algebra.Eq.to.Eq.swap, x, y)

    Eq << Eq[-1].this.rhs.limits_subs(i, j)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.swap)

    Eq << Eq.expansion.subs(Eq[-1].reversed)




if __name__ == '__main__':
    run()
# created on 2021-01-04
# updated on 2023-05-21
