from util import *


@apply
def apply(self):
    ((x, k), (n, S[k])), (k, S[0], S[n + 1]) = self.of(Sum[Pow * Stirling1])
    return Equal(self, RisingFactorial(x, n))


@prove
def prove(Eq):
    from Axiom import Discrete, Algebra

    k = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True, given=False)
    x = Symbol(real=True)
    Eq << apply(Sum[k:n + 1](x ** k * Stirling1(n, k)))

    # try to prove it by inspecting the recurrence relations of the coefficients!
    Eq << Eq[0].subs(n, n + 1)

    Eq << Eq[1].this.find(Stirling1).apply(Discrete.Stirling1.eq.Add.recurrence)

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Add)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.limits.subs.offset, 1)

    Eq << Eq[-1].this.find(Sum).find(Pow).apply(Algebra.Pow.eq.Mul.split.exponent)

    Eq << Eq[-1].this.lhs.apply(Algebra.Add.eq.Mul)

    Eq << Eq[0] * (x + n)

    Eq << Eq[-1].this.rhs.apply(Discrete.Mul.eq.RisingFactorial.push)

    Eq << Imply(Eq[0], Eq[1], plausible=True)

    Eq << Algebra.Imply.to.Eq.induct.apply(Eq[-1], n, 0)


if __name__ == '__main__':
    run()
# created on 2023-08-26
