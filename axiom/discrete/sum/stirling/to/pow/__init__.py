from util import *


@apply
def apply(self):
    ((x, k), (n, S[k])), (k, S[0], S[n + 1]) = self.of(Sum[FallingFactorial * Stirling])
    return Equal(self, x ** n)


@prove
def prove(Eq):
    from axiom import discrete, algebra

    k = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True, given=False)
    x = Symbol(real=True)
    Eq << apply(Sum[k:n + 1](FallingFactorial(x, k) * Stirling(n, k)))

    #try to prove it by inspecting the recurrence relations of the coefficients! We can induct on n:


    Eq << Eq[0].subs(n, n + 1)

    Eq << Eq[1].this.find(Stirling).apply(discrete.stirling.to.add.recurrence)

    Eq << Eq[-1].this.find(Mul).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.subs.offset, 1)

    Eq << Eq[0] * x

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.pow.add.exponent)

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.sum)

    Eq << Eq[-1].this.lhs().expr.args[:2].apply(discrete.mul.fallingFactorial.to.add)

    Eq << Eq[-1].this.find(Mul).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add)

    Eq << Infer(Eq[0], Eq[1], plausible=True)

    Eq << algebra.infer.imply.eq.induct.apply(Eq[-1], n, 0)




if __name__ == '__main__':
    run()
# created on 2023-08-26
from . import st
