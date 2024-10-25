from util import *


@apply
def apply(self, swap=None, reverse=None):
    (λ, γ), h = self.of(Mul ** Expr)
    n, = h.shape
    if swap:
        λ, γ = γ, λ

    if reverse:
        rhs = λ ** h @ (γ ** h * Identity(n))
    else:
        rhs = Identity(n) * λ ** h @ γ ** h
    return Equal(self, rhs)


@prove
def prove(Eq):
    from axiom import algebra, discrete

    h = Symbol(real=True, shape=(oo,))
    n = Symbol(integer=True, positive=True)
    λ, γ = Symbol(real=True)
    Eq << apply((λ * γ) ** h[:n], reverse=True)

    i = Symbol(domain=Range(n))
    Eq << algebra.eq.of.eq.getitem.apply(Eq[0], i)

    Eq << Eq[-1].this.find(MatMul).apply(discrete.matmul.to.sum)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.pow.mul.base)




if __name__ == '__main__':
    run()
# created on 2023-04-16
from . import delta
