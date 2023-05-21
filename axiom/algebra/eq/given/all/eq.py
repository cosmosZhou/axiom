from util import *


@apply
def apply(self, i=None):
    from axiom.algebra.eq.to.all.eq import rewrite
    return rewrite(self, i)


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f, g = Symbol(shape=(oo,), real=True)
    Eq << apply(Equal(Lamda[k:n](f[k]), Lamda[k:n](g[k])))

    Eq << Eq[0].this.apply(algebra.eq.to.all.eq)


if __name__ == '__main__':
    run()
# created on 2023-05-01
