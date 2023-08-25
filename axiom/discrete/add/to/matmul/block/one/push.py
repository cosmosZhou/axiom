from util import *


@apply
def apply(self):
    (a, X), x = self.of(MatMul + Expr)    
    n = X.shape[0]
    i = self.generate_var(integer=True)
    x_extended = Lamda[i:n + 1](X[i]).simplify()
    assert x_extended[n] == x
    
    return Equal(self, BlockMatrix(a, 1) @ x_extended)

@prove
def prove(Eq):
    from axiom import algebra, discrete

    t, k = Symbol(integer=True, positive=True)
    L = Symbol(shape=(oo, oo), super_complex=True)
    ξ = Symbol(r'{\color{red} {ξ}}', complex=True, shape=(oo,))
    Eq << apply(ξ[k + 1:t] @ L[k + 1:t, :k] + L[t, :k])

    Eq << Eq[0].this.rhs.args[1].apply(algebra.expr.to.block, t - k - 1)

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.block)


if __name__ == '__main__':
    run()
# created on 2023-06-27
