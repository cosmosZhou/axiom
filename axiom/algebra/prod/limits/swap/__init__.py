from util import *


@apply
def apply(self, i=0, j=1):
    from axiom.algebra.sum.limits.swap import rewrite
    return Equal(self, rewrite(Product, self, i, j))


@prove
def prove(Eq):
    from axiom import algebra

    i, j = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)
    n = Symbol(integer=True, positive=True, given=False)
    f = Symbol(shape=(oo,), real=True)
    g = Symbol(shape=(oo, oo), real=True)
    Eq << apply(Product[i:0:m, j:0:n](f[i] + g[i, j]))

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(algebra.prod.to.mul.split, cond={n})

    Eq << Eq[-1].this.lhs.find(Product).apply(algebra.prod.to.mul.doit.outer.setlimit)

    s = Symbol(Product[j:0:n + 1](f[i] + g[i, j]))
    Eq << s.this.definition

    Eq << Eq[-1].apply(algebra.eq.imply.eq.prod, (i, 0, m))

    Eq << Eq[-2].this.rhs.apply(algebra.prod.to.mul.split, cond={n})

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.prod.to.mul.prod)

    Eq << Eq[2].subs(Eq[-1].reversed)

    Eq << Eq[0] * Eq[-1].lhs.args[0]

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.infer.imply.eq.induct.apply(Eq[-1], n=n, start=1)




if __name__ == '__main__':
    run()

from . import subs
from . import intlimit
# created on 2020-03-07
# updated on 2023-07-02
