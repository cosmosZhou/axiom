from util import *


@apply
def apply(self, index=0, offset=None):
    from Axiom.Algebra.Sum.limits.subs.offset import limits_subs
    return Equal(self, limits_subs(MatProduct, self, index, offset), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Discrete, Algebra

    n, d = Symbol(integer=True)
    k = Symbol(integer=True, positive=True)
    f = Function(real=True, shape=(k, k))
    m = Symbol(integer=True, nonnegative=True, given=False)
    Eq << apply(MatProduct[n:m](f(n)), d)

    Eq << Eq[0].subs(m, 0)

    Eq.induct = Eq[0].subs(m, m + 1)

    Eq << Eq.induct.this.lhs.apply(Discrete.MatProd.eq.Dot.pop)

    Eq << Eq[-1].this.rhs.apply(Discrete.MatProd.eq.Dot.pop)

    Eq << Eq[0] @ f(m)

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Algebra.Imply.to.Cond.induct.apply(Eq[-1], n=m, start=0)


if __name__ == '__main__':
    run()
# created on 2020-08-30
