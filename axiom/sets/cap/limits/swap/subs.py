from util import *


@apply
def apply(self):
    from axiom.algebra.sum.limits.swap.subs import rewrite 
    return Equal(self, rewrite(Cap, self))


@prove
def prove(Eq):
    i, j, k = Symbol(integer=True)
    A = Symbol(etype=dtype.integer)
    n = Symbol(integer=True, positive=True)
    f = Function(integer=True)
    g = Symbol(shape=(oo, oo), etype=dtype.real)
    h = Symbol(shape=(oo,), etype=dtype.real)
    Eq << apply(Cap[i:f(j), j:A](h[i] | g[i, j]))

    Eq << Eq[-1].this.rhs.limits_subs(i, k)

    


if __name__ == '__main__':
    run()

# created on 2021-09-04
# updated on 2023-11-11
