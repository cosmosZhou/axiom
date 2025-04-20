from util import *


@apply
def apply(self, *, simplify=False):
    expr, *limits = self.of(Any)
    limit, *limits = limits
    assert limits
    expr = Any(expr, limit).simplify()
    return Any(expr, *limits, evaluate=simplify)


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Symbol(shape=(oo,), bool=True)
    g = Symbol(shape=(oo, oo), bool=True)
    Eq << apply(Any[i:n, j:n](f[j] & g[i, j]))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-1].this.lhs.expr.apply(Algebra.Any.And.of.Cond.Any, simplify=None)

    Eq << Eq[-2].this.rhs.expr.apply(Algebra.Cond.Any.given.Any.And, simplify=None)




if __name__ == '__main__':
    run()
# created on 2023-06-06
