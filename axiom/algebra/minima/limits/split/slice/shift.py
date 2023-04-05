from util import *


@apply
def apply(self, index=0):
    from axiom.algebra.sum.limits.split.slice.shift import rewrite
    return Equal(self, rewrite(Minima, self, index))


@prove(provable=False)
def prove(Eq):
    n = Symbol(integer=True, nonnegative=True)
    i = Symbol(domain=Range(n))
    x = Symbol(integer=True, shape=(oo,))
    f = Function(real=True, shape=())
    Eq << apply(Minima[x[i:n + 1]](f(x[i:n + 1])))


if __name__ == '__main__':
    run()
# created on 2023-03-27
