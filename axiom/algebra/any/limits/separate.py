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
    from axiom import algebra

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Symbol(shape=(oo,), bool=True)
    g = Symbol(shape=(oo, oo), bool=True)
    Eq << apply(Any[i:n, j:n](f[j] & g[i, j]))

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq << Eq[-1].this.lhs.expr.apply(algebra.cond.any.imply.any.et, simplify=None)

    Eq << Eq[-2].this.rhs.expr.apply(algebra.cond.any.given.any.et, simplify=None)

    


if __name__ == '__main__':
    run()
# created on 2023-06-06
