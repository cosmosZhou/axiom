from util import *


@apply
def apply(self):
    fx, (x, a, b) = self.of(Integral)

    return Equal(self, Piecewise((-Integral[x:Interval(b, a)](fx), a > b), (Integral[x:Interval(a, b)](fx), True)))


@prove
def prove(Eq):
    from Axiom import Calculus, Algebra

    x, a, b = Symbol(real=True)
    f = Function(real=True, integrable=True)
    Eq << apply(Integral[x:a:b](f(x)))

    Eq << Eq[0].this.rhs.find(Integral).apply(Calculus.Integral.eq.Piece.st.Interval)

    Eq << Eq[-1].this.rhs.args[1].expr.apply(Calculus.Integral.eq.Piece.st.Interval)

    Eq << Eq[-1].this.find(-Piecewise).apply(Algebra.Mul.eq.Piece)

    Eq << Eq[-1].this.rhs.apply(Algebra.Piece.unnest)

    Eq << Eq[-1].this.rhs.args[1].cond.reversed

    Eq << Eq[-1].this.rhs.args[0].expr.apply(Calculus.Neg.eq.Integral)

    Eq << Eq[-1].this.rhs.apply(Algebra.Piece.swap, -2)

    Eq << Algebra.Cond_Piece.of.Or.apply(Eq[-1])

    Eq << Eq[-1].this.find(And).apply(Algebra.Eq.Cond.of.And.subs)





if __name__ == '__main__':
    run()


# created on 2020-05-24
# updated on 2023-08-26
from . import st