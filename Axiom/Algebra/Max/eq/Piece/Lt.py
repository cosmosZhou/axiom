from util import *


@apply
def apply(self):
    arg, *args = self.of(Max)
    this = self.func(*args)
    rhs = Piecewise((arg, this < arg), (this, True))

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y, z = Symbol(real=True)
    Eq << apply(Max(x, y))

    Eq << Eq[0].this.rhs.apply(Algebra.Piece.swap)

    Eq << Eq[-1].lhs.this.apply(Algebra.Max.eq.Piece)

    Eq << Eq[-1].subs(x, z)

    Eq << Eq[-1].subs(y, x)
    Eq << Eq[-1].subs(z, y)


if __name__ == '__main__':
    run()
# created on 2019-06-18