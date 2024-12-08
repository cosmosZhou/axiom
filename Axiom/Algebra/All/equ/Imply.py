from util import *


@apply
def apply(given, *, simplify=True):
    fn1, *limits = given.of(All)
    cond = given.limits_cond
    if simplify:
        cond = cond.simplify()
    return Imply(cond, fn1)


@prove
def prove(Eq):
    from Axiom import Algebra
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))

    Eq << apply(All[n:Equal(f[n], g[n])](Equal(f[n + 1], g[n + 1])))

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.All.to.Imply)

    Eq << Eq[-1].this.rhs.apply(Algebra.All.of.Imply)


if __name__ == '__main__':
    run()
# created on 2018-12-22
