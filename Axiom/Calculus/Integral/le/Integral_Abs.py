from util import *


@apply
def apply(self):
    expr, *limits = self.of(Integral)
    return self <= Integral(Abs(expr), *limits)


@prove
def prove(Eq):
    from Axiom import Algebra, Calculus

    a, b = Symbol(real=True)
    x = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Integral[x:a:b](f(x)))


    Eq << Algebra.Le_Abs.apply(f(x))
    Eq << Calculus.Le.to.Le.Integral.apply(Eq[-1], (x, a, b))



if __name__ == '__main__':
    run()
# created on 2023-04-15