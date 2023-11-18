from util import *


@apply
def apply(self):
    from axiom.algebra.sum.limits.swap.subs import rewrite 
    return Equal(self, rewrite(Product, self))
    


@prove
def prove(Eq):
    i, j, k = Symbol(integer=True)
    A = Symbol(etype=dtype.integer)
    f = Function(integer=True)
    g = Symbol(shape=(oo, oo), real=True)
    h = Symbol(shape=(oo,), real=True)
    Eq << apply(Product[i:f(j), j:A](h[i] * g[i, j]))

    Eq << Eq[-1].this.rhs.limits_subs(i, k)

    


if __name__ == '__main__':
    run()

# created on 2021-08-11
# updated on 2023-11-11
