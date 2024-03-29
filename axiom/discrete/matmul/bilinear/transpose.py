from util import *


@apply
def apply(self):
    x, W, y = self.of(MatMul)
    return Equal(self, y @ W.T @ x)


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol(integer=True)
    x, y = Symbol(shape=(n,), real=True)
    W = Symbol(shape=(n, n), real=True)
    Eq << apply(x @ W @ y)

    i, j = Symbol(domain=Range(n))
    Eq << (x @ W).this.apply(discrete.matmul.to.lamda, var={i, j})

    Eq << Eq[-1] @ y

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.sum)

    Eq.expansion = Eq[-1].this.rhs.expr.apply(algebra.mul.to.sum)

    Eq << Eq.expansion.subs(W, W.T)

    Eq << Eq[-1].apply(algebra.eq.imply.eq.swap, x, y)

    Eq << Eq[-1].this.rhs.limits_subs(i, j)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.swap)

    Eq << Eq.expansion.subs(Eq[-1].reversed)

    


if __name__ == '__main__':
    run()
# created on 2021-01-04
# updated on 2023-05-21
