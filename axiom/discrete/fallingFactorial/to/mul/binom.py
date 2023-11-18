from util import *


@apply
def apply(self):
    x, i = self.of(FallingFactorial)
    return Equal(self, Factorial(i) * Binomial(x, i))


@prove
def prove(Eq):
    from axiom import discrete

    x = Symbol(real=True)
    n = Symbol(integer=True, nonnegative=True)
    Eq << apply(FallingFactorial(x, n))

    Eq << Eq[-1].this.find(Binomial).apply(discrete.binom.to.mul.fallingFactorial)

    


if __name__ == '__main__':
    run()
# created on 2023-08-27
