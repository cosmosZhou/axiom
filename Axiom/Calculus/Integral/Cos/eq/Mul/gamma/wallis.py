from util import *


@apply
def apply(self):
    (x, n), (S[x], S[0], S[pi / 2]) = self.of(Integral[Cos ** Expr])
    n += 1
    return Equal(self,
                 sqrt(pi) * Gamma(n / 2) / (2 * Gamma(n / 2 + S.One / 2)))


@prove
def prove(Eq):
    from Axiom import Calculus, Geometry, Algebra

    n = Symbol(integer=True, positive=True, given=False)
    x = Symbol(real=True)
    Eq << apply(Integral[x:0:pi / 2](cos(x) ** (n - 1)))

    (x, *_), *_ = Eq[0].lhs.limits
    Eq << Eq[0].subs(n, 1)

    Eq << Eq[-1].this.lhs.doit()

    Eq << Eq[0].subs(n, 2)

    Eq << Eq[-1].this.lhs.doit()

    Eq.induct = Eq[0].subs(n, n + 2)

    Eq << Eq.induct.lhs.this.expand()

    # Integration by parts
    Eq << Eq[-1].this.rhs.apply(Calculus.Integral.eq.Add.by_parts) / n

    Eq << Eq[-1].this.lhs.args[1].expr.powsimp()

    Eq << Eq[-1].this.rhs.expr.powsimp()

    Eq << Eq[-1].this.find(sin ** 2).apply(Geometry.Square.Sin.eq.Sub.Square.Cos)

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.rhs.expr.args[0].powsimp()

    Eq << Eq[-1].this.rhs.apply(Calculus.Integral.eq.Add)

    Eq << Eq[-1].this.find(Integral[-Expr]).simplify()

    Eq << Algebra.Eq.to.Eq.simple_equation.apply(Eq[-1], -Eq[-1].rhs.args[1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Div.cancel, n)

    Eq << Eq[-1].this.rhs.find(Integral).expr.apply(Algebra.Mul.eq.Pow.Add.exponent)

    Eq << Algebra.Eq.Eq.to.Eq.subs.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq.induct.this.rhs.expand(func=True)

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Algebra.Eq.Eq.Imply.to.Eq.induct.apply(Eq[1], Eq[2], Eq[-1], n=n, start=1)





if __name__ == '__main__':
    run()

# created on 2020-06-30
# updated on 2023-07-03