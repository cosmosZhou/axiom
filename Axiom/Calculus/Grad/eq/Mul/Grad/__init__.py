from util import *


@apply
def apply(self):
    expr, *limits_d = self.of(Derivative)
    (xi, S[1]), = limits_d
    x, i = xi.of(Indexed)

    vars = set()
    for var in expr.free_symbols:
        if var.has(x, i):
            continue
        vars.add(var)
    j, = vars
    expr = expr._subs(x[j], x[i])
    assert not expr._has(j)
    return Equal(self, KroneckerDelta(i, j) * Derivative(expr, *limits_d).doit())


@prove
def prove(Eq):
    from Axiom import Algebra, Calculus, Logic

    n = Symbol(integer=True, positive=True)
    f = Function(real=True)
    x = Symbol(real=True, shape=(n,))
    i, j = Symbol(integer=True)
    Eq << apply(Derivative[x[i]](f(x[j])))

    Eq << Eq[-1].this.find(KroneckerDelta).apply(Algebra.Delta.eq.Ite)

    Eq << Logic.Cond.given.And.Imp.split.apply(Eq[-1], cond=Eq[-1].find(Equal))

    Eq <<= Logic.Imp.given.Imp.subs.Bool.apply(Eq[-2]), Logic.Imp.given.Imp.subs.Bool.apply(Eq[-1], invert=True)

    Eq << Logic.Imp.given.Imp.subs.apply(Eq[-2])

    Eq << Eq[-1].this.lhs.apply(Calculus.EqZero.of.Ne, f, x)





if __name__ == '__main__':
    run()
# created on 2023-03-18
# updated on 2023-03-19
del Log
from . import Log
