from util import *


@apply
def apply(self, index=0):
    from Axiom.Algebra.Sum.limits.pop.Slice import rewrite
    return Equal(self, rewrite(Integral, self, index))


@prove
def prove(Eq):
    from Axiom import Calculus

    n = Symbol(integer=True, nonnegative=True)
    i = Symbol(domain=Range(n))
    x = Symbol(integer=True, shape=(oo,))
    f = Function(real=True, shape=())
    Eq << apply(Integral[x[i:n + 1]](f(x[i:n + 1])))

    Eq << Eq[0].this.rhs.apply(Calculus.Integral.limits.concat)


if __name__ == '__main__':
    run()
# created on 2023-03-27
# updated on 2023-11-18
