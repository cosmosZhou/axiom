from util import *


@apply
def apply(self, index=0):
    from axiom.algebra.sum.limits.concat import rewrite
    return Equal(self, rewrite(Integral, self, index))


@prove
def prove(Eq):
    from axiom import calculus

    n = Symbol(integer=True, positive=True)
    i = Symbol(domain=Range(n - 1))
    x = Symbol(real=True, shape=(oo,))
    f = Function(real=True, shape=())
    Eq << apply(Integral[x[i], x[i + 1:n + 1]](f(x[i:n])))

    Eq << Eq[0].this.rhs.apply(calculus.integral.limits.shift.slice)




if __name__ == '__main__':
    run()
# created on 2023-03-28
