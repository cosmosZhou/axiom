from util import *


@apply
def apply(self):
    expr, (x, domain) = self.of(Integral)
    a, b = domain.of(Interval)
    return Equal(self, Integral[x:a:b](expr) * Bool(a <= b))


@prove
def prove(Eq):
    from Axiom import Calculus, Algebra, Sets

    x, a, b = Symbol(real=True)
    f = Function(real=True, continuous=True)
    Eq << apply(Integral[x:Interval(a, b)](f(x)))

    Eq << Eq[0].this.rhs.find(Integral).apply(Calculus.Integral.eq.Piece)

    Eq << Eq[-1].this.rhs.find(Bool).apply(Algebra.Bool.eq.Piece)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.Piece.eq.Piece)

    Eq << Algebra.Cond_Piece.of.And.Imply.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Sets.Gt.to.Eq_EmptySet.Interval)

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-06-19
