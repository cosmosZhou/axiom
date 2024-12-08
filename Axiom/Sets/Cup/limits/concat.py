from util import *


@apply
def apply(self, index=0):
    from Axiom.Algebra.Sum.limits.concat import rewrite
    return Equal(self, rewrite(Cup, self, index))


@prove
def prove(Eq):
    from Axiom import Sets

    n = Symbol(integer=True, positive=True)
    i = Symbol(domain=Range(n - 1))
    x = Symbol(integer=True, shape=(oo,))
    f = Function(etype=dtype.real, shape=())
    Eq << apply(Cup[x[i], x[i + 1:n + 1]](f(x[i:n])))

    Eq << Eq[0].this.rhs.apply(Sets.Cup.limits.shift.Slice)




if __name__ == '__main__':
    run()
# created on 2023-11-18
