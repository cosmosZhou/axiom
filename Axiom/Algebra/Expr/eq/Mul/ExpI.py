from util import *


@apply
def apply(self):
    return Equal(self, abs(self) * exp(S.ImaginaryUnit * Arg(self)))


@prove
def prove(Eq):
    from Axiom import Calculus, Algebra, Geometry

    z = Symbol(complex=True, given=True)
    Eq << apply(z)

    Eq << Eq[0].this.find(Exp).apply(Geometry.ExpI.eq.Add.Euler)

    Eq << Eq[-1].this.lhs.apply(Algebra.Expr.eq.Add.complex)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.eq.Add)

    Eq << Algebra.Eq.of.And.Eq.complex.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(Geometry.Re.eq.Mul.Cos)
    Eq << Eq[-1].this.lhs.apply(Geometry.Im.eq.Mul.Sin)


if __name__ == '__main__':
    run()
# created on 2018-07-26
