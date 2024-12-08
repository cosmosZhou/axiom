from util import *


@apply
def apply(self):
    expr, *limits = self.of(Integral)
    return abs(self) <= Integral(abs(expr), *limits)


@prove
def prove(Eq):
    from Axiom import Algebra, Calculus

    f = Function(real=True, continuous=True)
    x, a, b = Symbol(real=True)
    Eq << apply(Integral[x:a:b](f(x)))

    Eq << Algebra.LeAbs.of.And.apply(Eq[0])

    Eq << Algebra.Le_Abs.apply(f(x))

    Eq << Calculus.Le.to.Le.Integral.apply(Eq[-1], (x, a, b))

    Eq << Algebra.Ge_NegAbs.apply(f(x))

    Eq << Calculus.Ge.to.Ge.Integral.apply(Eq[-1], (x, a, b))




if __name__ == '__main__':
    run()
# created on 2023-04-03
