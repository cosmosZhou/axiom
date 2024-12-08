from util import *


@apply
def apply(is_nonnegative, self, offset):
    expr = is_nonnegative.of(Expr >= 0)
    S[expr], (x, *ab) = self.of(Integral)
    if ab:
        a, b = ab
        limit = (x, a - offset, b - offset)
    else:
        limit = (x,)

    return Equal(self, Integral(expr._subs(x, x + offset), limit))


@prove
def prove(Eq):
    from Axiom import Algebra, Calculus

    x, a, b, d = Symbol(real=True)
    f = Function(real=True, integrable=True)
    Eq << apply(f(x) >= 0, Integral[x:a:b](f(x)), d)

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=a > b)

    Eq <<= Eq[-2].this.find(Integral).apply(Calculus.Integral.eq.Piece), Eq[-1].this.find(Integral).apply(Calculus.Integral.eq.Piece)

    Eq <<= Eq[-2].this.find(Equal[~Integral]).apply(Calculus.Integral.eq.Piece), Eq[-1].this.find(Equal[~Integral]).apply(Calculus.Integral.eq.Piece)

    Eq <<= Algebra.Imply.of.Imply.subs.Bool.apply(Eq[-2]), Algebra.Imply.of.Imply.subs.Bool.apply(Eq[-1], invert=True)

    Eq << -Eq[-2].this.rhs

    Eq << Algebra.Cond.to.And.Imply.split.apply(Eq[0], cond=a > b)

    Eq << Eq[-2].this.rhs.apply(Calculus.Ge_0.to.Eq.Integral.limits.offset.Interval, Eq[-3].find(Integral), d)

    Eq << Eq[-1].this.rhs.apply(Calculus.Ge_0.to.Eq.Integral.limits.offset.Interval, Eq[-4].find(Integral), d)


if __name__ == '__main__':
    run()
# created on 2020-05-25

del Interval
from . import Interval
