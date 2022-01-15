from util import *


@apply
def apply(self):
    fx, (x, a, b) = self.of(-Integral)

    return Equal(self, Integral[x:b:a](fx), evaluate=False)


@prove
def prove(Eq):
    from axiom import calculus

    x, a, b = Symbol(real=True)
    f = Function(real=True, integrable=True)
    Eq << apply(-Integral[x:a:b](f(x)))
    Eq << Eq[0].this.rhs.apply(calculus.integral.to.neg)


if __name__ == '__main__':
    run()
# created on 2020-05-24
