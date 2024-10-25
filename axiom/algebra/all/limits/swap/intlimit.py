from util import *


@apply
def apply(self):
    from axiom.algebra.sum.limits.swap.intlimit import limits_swap
    return limits_swap(All, self)


@prove
def prove(Eq):
    from axiom import algebra, sets

    i, j, d, a = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Symbol(shape=(oo,), bool=True)
    g = Symbol(shape=(oo, oo), bool=True)
    Eq << apply(All[i:a + d:j + d, j:a + 1:n](f[i] & g[i, j]))

    Eq << Eq[0].this.lhs.apply(algebra.all.to.ou)

    Eq << Eq[-1].this.rhs.apply(algebra.all.to.ou)

    Eq << sets.el.el.transform.i_lt_j.apply(*Or(*Eq[-1].find(Or).args[:-1]).invert().args)

    Eq << Eq[-1].this.apply(algebra.iff.contraposition).reversed

    Eq << algebra.iff.then.iff.ou.apply(Eq[-1], cond=Eq[0].lhs.expr)





if __name__ == '__main__':
    run()
# created on 2022-01-24
# updated on 2023-05-21
