from util import *


@apply
def apply(self):
    x, (S[x], k) = self.of(Expr * FallingFactorial)
    assert k >= 0 and k.is_integer
    return Equal(self, FallingFactorial(x, k + 1) + k * FallingFactorial(x, k))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    x = Symbol(complex=True)
    k = Symbol(integer=True, nonnegative=True)
    Eq << apply(x * FallingFactorial(x, k))

    Eq << FallingFactorial(x, k + 1).this.apply(discrete.fallingFactorial.to.mul.pop)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.apply(algebra.eq.transport, rhs=-1)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2023-08-26
