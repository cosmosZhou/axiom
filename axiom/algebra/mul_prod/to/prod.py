from util import *


@apply
def apply(self):
    from axiom.algebra.add.to.sum import piece_together
    return Equal(self, piece_together(Product, self))


@prove
def prove(Eq):
    from axiom import algebra

    k, i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f, g = Function(integer=True)
    Eq << apply(Product[i:k, k:n](f(k, i)) * Product[j:k, k:n](g(k, j)))

    Eq << Eq[-1].this.rhs.apply(algebra.prod.to.mul.prod)

    


if __name__ == '__main__':
    run()

# created on 2018-04-14
# updated on 2023-08-20
