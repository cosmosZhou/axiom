from util import *


@apply
def apply(self, i=0, j=1):
    from Axiom.Algebra.Sum.limits.swap import rewrite
    return Equal(self, rewrite(Product, self, i, j))


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    i, j = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)
    n = Symbol(integer=True, positive=True, given=False)
    f = Symbol(shape=(oo,), real=True)
    g = Symbol(shape=(oo, oo), real=True)
    Eq << apply(Product[i:m, j:n](f[i] + g[i, j]))

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(Algebra.Prod.eq.Mul.split, cond={n})

    Eq << Eq[-1].this.lhs.find(Product).apply(Algebra.Prod.eq.Mul.doit.outer.setlimit)

    s = Symbol(Product[j:n + 1](f[i] + g[i, j]))
    Eq << s.this.definition

    Eq << Eq[-1].apply(Algebra.EqProd.of.Eq, (i, 0, m))

    Eq << Eq[-2].this.rhs.apply(Algebra.Prod.eq.Mul.split, cond={n})

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Prod.eq.Mul.Prod)

    Eq << Eq[2].subs(Eq[-1].reversed)

    Eq << Eq[0] * Eq[-1].lhs.args[0]

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Logic.Eq.of.Imp.induct.apply(Eq[-1], n=n, start=1)




if __name__ == '__main__':
    run()

# created on 2020-03-07
# updated on 2023-07-02
from . import subs
from . import intlimit
