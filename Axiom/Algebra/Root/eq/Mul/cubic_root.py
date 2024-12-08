from util import *


@apply
def apply(self):
    p = self.of((Expr ** 3) ** (S.One / 3))
    return Equal(self, p * exp(-S.ImaginaryUnit * 2 * S.Pi / 3 * Ceiling(3 * Arg(p) / (2 * S.Pi) - S.One / 2)))


@prove
def prove(Eq):
    from Axiom import Algebra

    p = Symbol(complex=True, given=True)
    Eq << apply((p ** 3) ** (S.One / 3))

    Eq << Eq[0].this.lhs.apply(Algebra.Root.eq.Mul.ExpI.Arg)

    Eq << Eq[-1].this.find(Arg).apply(Algebra.Arg.Pow.eq.Add)

    Eq << Eq[-1].this.find(Exp[~Mul]).apply(Algebra.Mul.eq.Add)
    Eq << Eq[-1].this.find(Exp).apply(Algebra.Exp.eq.Mul)

    Eq << Eq[-1].this.rhs.apply(Algebra.Expr.eq.Mul.ExpI)


if __name__ == '__main__':
    run()
# created on 2020-03-11
