from util import *


def rewrite(Sum, self, i=0, j=1):
    assert i < j
    expr, *limits = self.of(Sum)
    i_limit, j_limit = limits[i], limits[j]

    assert not i_limit._has(j_limit[0])
    if j_limit._has(i_limit[0]):
        i = self.expr.generate_var(excludes=self.variables, **i_limit[0].type.dict)
        expr = expr._subs(i_limit[0], i)
        i_limit = (i, *i_limit[1:])

    limits[i], limits[j] = j_limit, i_limit
    return Sum(expr, *limits)

@apply
def apply(self, i=0, j=1):
    return Equal(self, rewrite(Sum, self, i, j))


@prove
def prove(Eq):
    from axiom import algebra

    i, j = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)
    n = Symbol(integer=True, positive=True, given=False)
    f = Symbol(shape=(oo,), real=True)
    g = Symbol(shape=(oo, oo), real=True)
    Eq << apply(Sum[i:m, j:n](f[i] * g[i, j]))

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(algebra.sum.to.add.split, cond={n})

    s = Symbol(Sum[j:n + 1](f[i] * g[i, j]))
    Eq << s.this.definition

    Eq << Eq[-1].apply(algebra.eq.then.eq.sum, (i, 0, m))

    Eq << Eq[-2].this.rhs.apply(algebra.sum.to.add.split, cond={n})

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.mul.to.sum)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add)

    Eq << Eq[1].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.apply(algebra.eq.simplify.terms.common)

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.infer.then.eq.induct.apply(Eq[-1], n=n, start=1)





if __name__ == '__main__':
    run()

from . import intlimit
from . import subs
# created on 2018-04-30
# updated on 2023-08-26
