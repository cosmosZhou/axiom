from util import *


@apply
def apply(self):
    (num, den), *limits_d = self.of(Derivative[Expr / Expr])    
    return Equal(self, (Derivative(num, *limits_d) * den - num * Derivative(den, *limits_d))/ den ** 2)


@prove
def prove(Eq):
    from axiom import calculus, algebra

    x = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Derivative[x](f(x) / g(x)))

    Eq << Eq[0].this.lhs.apply(calculus.grad.mul.to.add)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Derivative).doit()

    


if __name__ == '__main__':
    run()
# created on 2023-11-26
