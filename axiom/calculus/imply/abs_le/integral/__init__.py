from util import *


@apply
def apply(self):
    expr, *limits = self.of(Integral)
    return Abs(self) <= Integral(Abs(expr), *limits)


@prove
def prove(Eq):
    from axiom import algebra, calculus

    f = Function(real=True, continuous=True)
    x, a, b = Symbol(real=True)
    Eq << apply(Integral[x:a:b](f(x)))

    Eq << algebra.abs_le.given.et.apply(Eq[0])

    Eq << algebra.imply.le.abs.apply(f(x))

    Eq << calculus.le.imply.le.integral.apply(Eq[-1], (x, a, b))

    Eq << algebra.imply.ge.abs.apply(f(x))

    Eq << calculus.ge.imply.ge.integral.apply(Eq[-1], (x, a, b))

    


if __name__ == '__main__':
    run()
# created on 2023-04-03
from . import abs
