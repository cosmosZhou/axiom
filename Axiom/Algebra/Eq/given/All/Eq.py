from util import *


@apply
def apply(self, i=None):
    from Axiom.Algebra.Eq.Is.All.Eq import rewrite
    return rewrite(self, i)


@prove
def prove(Eq):
    from Axiom import Algebra

    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f, g = Symbol(shape=(oo,), real=True)
    Eq << apply(Equal(Lamda[k:n](f[k]), Lamda[k:n](g[k])))

    Eq << Eq[0].this.apply(Algebra.Eq.Is.All.Eq)


if __name__ == '__main__':
    run()
# created on 2023-05-01
