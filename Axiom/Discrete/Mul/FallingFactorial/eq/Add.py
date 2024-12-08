from util import *


@apply
def apply(self):
    x, (S[x], k) = self.of(Expr * FallingFactorial)
    assert k >= 0 and k.is_integer
    return Equal(self, FallingFactorial(x, k + 1) + k * FallingFactorial(x, k))


@prove
def prove(Eq):
    from Axiom import Discrete, Algebra

    x = Symbol(complex=True)
    k = Symbol(integer=True, nonnegative=True)
    Eq << apply(x * FallingFactorial(x, k))

    Eq << FallingFactorial(x, k + 1).this.apply(Discrete.FallingFactorial.eq.Mul.pop)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.apply(Algebra.Eq.transport, rhs=-1)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2023-08-26
