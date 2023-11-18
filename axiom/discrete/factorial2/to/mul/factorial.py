from util import *


@apply
def apply(self):
    n = self.of(Factorial2)
    assert n.is_even
    assert n >= 0
    n /= 2
    return Equal(self, Factorial(n) * 2 ** n)


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol(integer=True, nonnegative=True)
    Eq << apply(Factorial2(n * 2))

    Eq << Eq[-1].this.lhs.apply(discrete.factorial2.to.prod)

    Eq << Eq[-1].this.lhs.apply(algebra.prod.to.mul.scale, S.Half)

    Eq << Eq[-1].this.rhs.apply(discrete.factorial.to.prod)

    i = Eq[-1].lhs.variable
    Eq << Eq[-1].this.lhs.apply(algebra.prod.limits.subs.negate, i, n - i)
    # https://en.wikipedia.org/wiki/Double_factorial
    


if __name__ == '__main__':
    run()
# created on 2023-06-03
