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
    from Axiom import Algebra

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Symbol(shape=(oo,), bool=True)
    g = Symbol(shape=(oo, oo), bool=True)
    Eq << apply(All[i:n, j:n](f[j] & g[i, j]))

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-1].this.lhs.expr.apply(Algebra.Cond.All.to.All.And, simplify=None)

    Eq << Eq[-2].this.rhs.expr.apply(Algebra.Cond.All.of.All.And, simplify=None)




if __name__ == '__main__':
    run()
# created on 2023-06-06