from util import *


@apply
def apply(self, i=0, j=1):
    from axiom.algebra.sum.limits.swap import rewrite
    return Equal(self, rewrite(Cap, self, i, j))


@prove
def prove(Eq):
    from axiom import sets, algebra

    i, j = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)
    n = Symbol(integer=True, positive=True, given=False)
    f = Symbol(shape=(oo,), etype=dtype.real)
    g = Symbol(shape=(oo, oo), etype=dtype.real)
    Eq << apply(Cap[i:0:m, j:0:n](f[i] | g[i, j]))

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(sets.cap.to.intersect.split, {n})

    Eq.induct_dissected = Eq[-1].this.find(Intersection[~Cap]).apply(sets.cap.to.intersect.doit.outer.setlimit)

    s = Symbol(Cap[j:0:n + 1](f[i] | g[i, j]))
    Eq << s.this.definition

    Eq << Eq[-1].apply(sets.eq.imply.eq.cap, (i, 0, m))

    Eq << Eq[-2].this.rhs.apply(sets.cap.to.intersect.split, {n})

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(sets.cap.to.intersect)

    Eq << Eq.induct_dissected.subs(Eq[-1].reversed)

    Eq << sets.eq.imply.eq.intersect.apply(Eq[0], Eq[-1].find(Cap))

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.infer.imply.eq.induct.apply(Eq[-1], n=n, start=1)

    
    


if __name__ == '__main__':
    run()

from . import intlimit
from . import subs
# created on 2021-01-31
# updated on 2023-07-02
