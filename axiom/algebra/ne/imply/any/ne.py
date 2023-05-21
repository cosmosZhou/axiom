from util import *


@apply
def apply(self, i=None):
    from axiom.algebra.ne.to.any.ne import rewrite
    return rewrite(self, i)


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=True)
    f, g = Symbol(shape=(oo,), real=True, given=True)
    Eq << apply(Unequal(Lamda[k:n](f[k]), Lamda[k:n](g[k])))

    Eq << ~Eq[1]

    Eq << algebra.all_eq.imply.eq.lamda.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.lhs.apply(algebra.expr.to.lamda, k)

    Eq << Eq[-1].this.rhs.apply(algebra.expr.to.lamda, k, simplify=None)

    Eq << ~Eq[-1]
    


if __name__ == '__main__':
    run()
# created on 2023-05-01
