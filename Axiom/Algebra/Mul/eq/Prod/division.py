from util import *


@apply
def apply(self):
    (fx, *limits), (gx, *S[limits]) = self.of(Product / Product)

    return Equal(self, Product(fx / gx, *limits))


@prove
def prove(Eq):
    from Axiom import Algebra
    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f, g = Function(integer=True)
    Eq << apply(Product[k:n](f(k)) / Product[k:n](g(k)))

    Eq << Eq[0].this.find(1 / Product).apply(Algebra.Pow.eq.Prod)

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul.Prod.eq.Prod)


if __name__ == '__main__':
    run()
# created on 2020-01-31
