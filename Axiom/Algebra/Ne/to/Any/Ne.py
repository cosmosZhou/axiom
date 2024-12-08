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

    Eq << ~Eq[1]

    Eq << Algebra.All_Eq.to.Eq.Lamda.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.lhs.apply(Algebra.Expr.eq.Lamda, k)

    Eq << Eq[-1].this.rhs.apply(Algebra.Expr.eq.Lamda, k, simplify=None)

    Eq << ~Eq[-1]



if __name__ == '__main__':
    run()
# created on 2023-05-01
