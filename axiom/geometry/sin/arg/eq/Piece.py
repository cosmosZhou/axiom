from util import *


@apply
def apply(self):
    z = self.of(Sin[Arg])
    x = Re(z)
    y = Im(z)
    r = sqrt(x ** 2 + y ** 2)
    return Equal(self, Piecewise((0, Equal(z, 0)), (y / r, True)))


@prove
def prove(Eq):
    from Axiom import Algebra, Geometry

    z = Symbol(complex=True, given=True)
    Eq << apply(sin(Arg(z)))

    Eq << Algebra.Expr.eq.Add.complex.apply(z)

    Eq << Algebra.Eq.to.Eq.Arg.apply(Eq[1])

    Eq << Eq[-1].this.rhs.apply(Geometry.Arg.eq.Piece.Asin)

    Eq << Geometry.Eq.to.Eq.Sin.apply(Eq[-1])

    Eq << Eq[0].this.find(Equal).apply(Algebra.Eq_0.equ.And.Eq_0)


if __name__ == '__main__':
    run()
# created on 2018-07-25
