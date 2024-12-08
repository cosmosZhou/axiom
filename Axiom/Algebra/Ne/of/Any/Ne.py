from util import *


@apply
def apply(self, i=None):
    from Axiom.Algebra.Ne.equ.Any.Ne import rewrite
    return rewrite(self, i)


@prove
def prove(Eq):
    from Axiom import Algebra

    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=True)
    f, g = Symbol(shape=(oo,), real=True, given=True)
    Eq << apply(Unequal(Lamda[k:n](f[k]), Lamda[k:n](g[k])))

    Eq << ~Eq[0]


    Eq << Algebra.Eq.to.All.Eq.apply(Eq[-1], simplify=None)
    Eq << ~Eq[-1]



if __name__ == '__main__':
    run()
# created on 2023-05-01
