from util import *


@apply
def apply(self, *, simplify=True):
    z, m = self.of(Pow[Expr, Expr ** -1])
    assert m > 0
    arg = Arg(z)
    if simplify:
        arg = arg.simplify()
    return Equal(self, abs(z) ** (1 / m) * exp(S.ImaginaryUnit * arg / m))


@prove
def prove(Eq):
    from Axiom import Algebra

    z = Symbol(real=True)
    n = Symbol(integer=True, positive=True)
    Eq << apply(z ** (1 / n))

    Eq << Eq[-1].this.lhs.base.apply(Algebra.Expr.eq.Mul.ExpI)

    Eq << Eq[-1].this.lhs.apply(Algebra.Pow.eq.Mul.split.base)

    Eq << Algebra.Eq.of.Eq.Div.apply(Eq[-1], Eq[-1].lhs.args[0])

    Eq << Eq[-1].this.lhs.apply(Algebra.Pow.Exp.eq.Exp)

    Eq << Eq[-1].this.lhs.find(Arg).simplify()

    # Eq << Eq[-1].this.lhs.find(Arg).apply(Algebra.arg_expi.to.add.ceiling)
    # Eq << Eq[-1].this.find(Ceiling).apply(Algebra.Ceiling.to.Zero.arg)


if __name__ == '__main__':
    run()
# created on 2018-08-22
