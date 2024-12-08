from util import *


@apply
def apply(self):
    x = self.of(Exp[ImaginaryUnit * Expr])
    return Equal(self, cos(x) + S.ImaginaryUnit * sin(x))


@prove
def prove(Eq):
    from Axiom import Calculus, Algebra, Geometry

    x = Symbol(real=True)
    Eq << apply(exp(S.ImaginaryUnit * x))

    i = S.ImaginaryUnit
    Eq << Calculus.Exp.eq.Sum.maclaurin.apply(i * x)

    n = Eq[-1].rhs.variable
    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Add.split, cond=Equal(n % 2, 0))

    Eq << Eq[-1].this.rhs.args[0].apply(Algebra.Sum.halve)

    Eq << Eq[-1].this.rhs.args[0].apply(Algebra.Sum.halve)

    Eq << Eq[-1].this.rhs.args[0].expr.expand()

    Eq.expand = Eq[-1].this.rhs.args[0].expr.expand()

    Eq << Geometry.Cos.eq.Sum.apply(cos(x))

    Eq << Geometry.Sin.eq.Sum.apply(sin(x))

    Eq << Eq[-2] + i * Eq[-1]

    Eq << Eq[-1].this.rhs.args[0].args[1].expr.expand()

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq.expand, Eq[-1])





if __name__ == '__main__':
    run()

# created on 2018-06-02

# updated on 2023-05-30
