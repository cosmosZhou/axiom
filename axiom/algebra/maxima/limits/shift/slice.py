from util import *


@apply
def apply(self, index=0):
    from axiom.algebra.sum.limits.shift.slice import rewrite
    return Equal(self, rewrite(Maxima, self, index))


@prove
def prove(Eq):
    n = Symbol(integer=True, nonnegative=True)
    i = Symbol(domain=Range(n))
    x = Symbol(integer=True, shape=(oo,))
    f = Function(real=True, shape=())
    Eq << apply(Maxima[x[i:n + 1]](f(x[i:n + 1])))

    Eq << Eq[0].this.rhs.simplify()


if __name__ == '__main__':
    run()
# created on 2023-03-27
# updated on 2023-07-02
