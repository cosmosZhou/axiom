from util import *


@apply
def apply(self):
    x, i = self.of(RisingFactorial)
    return Equal(self, (-1) ** i * FallingFactorial(-x, i))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    x = Symbol(real=True)
    n = Symbol(integer=True, nonnegative=True)
    Eq << apply(RisingFactorial(x, n))

    Eq << Eq[0].this.lhs.apply(discrete.risingFactorial.to.prod)

    Eq << Eq[-1].this.find(FallingFactorial).apply(discrete.fallingFactorial.to.prod)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.prod.distribute)

    


if __name__ == '__main__':
    run()
# created on 2023-08-20
