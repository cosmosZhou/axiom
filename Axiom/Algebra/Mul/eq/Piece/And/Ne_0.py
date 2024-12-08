from util import *


@apply
def apply(self):
    args = self.of(Mul)
    return Equal(self, Piecewise((self, And(*(Unequal(arg, 0) for arg in args))), (0, True)))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(real=True)
    Eq << apply(x * y)

    Eq << Algebra.Cond_Piece.of.Or.apply(Eq[0])

    Eq << Eq[-1].this.args[1].apply(Algebra.Ne_0.Ne_0.of.Ne_0)

    Eq << Eq[-1].this.find(Or).apply(Algebra.Or_Eq_0.of.Eq_.Mul.Zero)





if __name__ == '__main__':
    run()
# created on 2018-01-30
# updated on 2023-05-10
