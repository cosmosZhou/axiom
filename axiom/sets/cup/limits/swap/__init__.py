from util import *


@apply
def apply(self, i=0, j=1):
    from axiom.algebra.sum.limits.swap import rewrite
    return Equal(self, rewrite(Cup, self, i, j))


@prove
def prove(Eq):
    from axiom import sets, algebra

    i, j = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)
    n = Symbol(integer=True, positive=True, given=False)
    f = Symbol(shape=(oo,), etype=dtype.real)
    g = Symbol(shape=(oo, oo), etype=dtype.real)
    Eq << apply(Cup[i:0:m, j:0:n](f[i] & g[i, j]))

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(sets.cup.to.union.split, cond={n})

    Eq.induct_dissected = Eq[-1].this.find(Union[~Cup]).apply(sets.cup.to.union.doit.outer.setlimit)

    s = Symbol(Cup[j:0:n + 1](f[i] & g[i, j]))
    Eq << s.this.definition

    Eq << Eq[-1].apply(sets.eq.imply.eq.cup, (i, 0, m))

    Eq << Eq[-2].this.rhs.apply(sets.cup.to.union.split, cond={n})

    Eq << Eq[-1].this.rhs.args[1].apply(sets.intersect.to.cup)

    Eq << Eq[-1].this.find(Intersection[~Cup]).apply(sets.cup.to.union.doit.setlimit, simplify=None, evaluate=False)

    Eq << Eq[-4].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(sets.cup.to.union)

    Eq << Eq.induct_dissected.subs(Eq[-1].reversed)

    Eq << sets.eq.imply.eq.union.apply(Eq[0], Eq[-1].find(Cup))

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.infer.imply.eq.induct.apply(Eq[-1], n=n, start=1)

    
    


if __name__ == '__main__':
    run()

from . import intlimit
from . import subs
# created on 2021-02-11
# updated on 2023-07-02
