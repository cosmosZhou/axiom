from util import *


@apply
def apply(self, *, simplify=False):
    expr, *limits = self.of(All)
    limit, *limits = limits
    assert limits
    expr = All(expr, limit).simplify()
    return All(expr, *limits, evaluate=simplify)


@prove
def prove(Eq):
    from axiom import algebra

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Symbol(shape=(oo,), bool=True)
    g = Symbol(shape=(oo, oo), bool=True)
    Eq << apply(All[i:0:n, j:0:n](f[j] & g[i, j]))

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq << Eq[-1].this.lhs.expr.apply(algebra.cond.all.imply.all.et, simplify=None)

    Eq << Eq[-2].this.rhs.expr.apply(algebra.cond.all.given.all.et, simplify=None)

    


if __name__ == '__main__':
    run()
# created on 2023-06-06
