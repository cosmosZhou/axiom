from util import *


@apply
def apply(self, index=0):
    from axiom.algebra.sum.limits.pop.slice import rewrite
    return rewrite(Any, self, index)


@prove
def prove(Eq):
    n = Symbol(integer=True, nonnegative=True)
    i = Symbol(domain=Range(n))
    x = Symbol(integer=True, shape=(oo,))
    f = Function(real=True, bool=True)
    Eq << apply(Any[x[i:n + 1]](f(x[i:n + 1])))
    
    Eq << Eq[0].this.rhs.simplify()


if __name__ == '__main__':
    run()
# created on 2023-07-02
