from util import *


@apply
def apply(f0, suffice, n=None, start=0):
    start = sympify(start)
    fn, fn1 = suffice.of(Imply)
    assert fn._subs(n, n + 1) == fn1

    assert fn._subs(n, start) == f0
    a = n.domain.min()
    if a == start:
        return fn
    if a < start:
        diff = start - a
        if diff.is_Number:
            for i in range(diff):
                if fn._subs(n, a + i):
                    continue
                return
            return fn


@prove
def prove(Eq):
    from Axiom import Algebra
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))

    Eq << apply(LessEqual(f[0], g[0]), Imply(LessEqual(f[n], g[n]), LessEqual(f[n + 1], g[n + 1])), n=n)

    h = Symbol(Lamda[n](Bool(f[n] <= g[n])))

    Eq << h[0].this.definition

    Eq << Algebra.Cond.to.Eq.Bool.apply(Eq[0])

    Eq.initial = Algebra.Eq.Eq.to.Eq.trans.apply(Eq[-2], Eq[-1])

    Eq.suffice = Imply(Equal(h[n], 1), Equal(h[n + 1], 1), plausible=True)

    Eq << Eq.suffice.this.lhs.lhs.definition

    Eq << Eq[-1].this.lhs.lhs.apply(Algebra.Bool.eq.Piece)

    Eq << Eq[-1].this.rhs.lhs.definition

    Eq << Eq[-1].this.rhs.lhs.apply(Algebra.Bool.eq.Piece)

    Eq << Algebra.Eq.Imply.to.Eq.induct.apply(Eq.initial, Eq.suffice, n=n)

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.lhs.apply(Algebra.Bool.eq.Piece)


if __name__ == '__main__':
    run()

# created on 2018-04-18

from . import second
from . import split
